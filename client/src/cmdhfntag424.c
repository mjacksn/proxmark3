//-----------------------------------------------------------------------------
// Copyright (C) Proxmark3 contributors. See AUTHORS.md for details.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// See LICENSE.txt for the text of the license.
//-----------------------------------------------------------------------------
// High frequency ISO14443A / NTAG424 DNA Commands
//-----------------------------------------------------------------------------

#include "cmdhfntag424.h"
#include <ctype.h>
#include "cmdparser.h"
#include "cmdhf14a.h"
#include "iso7816/apduinfo.h"  // GetAPDUCodeDescription
#include "commonutil.h"
#include "protocols.h"
#include "cliparser.h"
#include "cmdmain.h"
#include "fileutils.h"          // saveFile
#include "crypto/libpcrypto.h"  // aes_decode
#include "cmac.h"


#define NTAG424_MAX_BYTES  412

static int CmdHelp(const char *Cmd);

typedef enum {
    NTAG424_AES,
    NTAG424_LRP,
} ntag424_auth_type_t;

typedef enum {
    NTAG424_KEY_APP_MASTER = 0x00,
    NTAG424_KEY_APP,
    NTAG424_SDM_META_READ,
    NTAG424_SDM_FILE_READ,
    NTAG424_ORIGINALITY
} ntag424_key_type_t;

typedef enum {
    NTAG413DNA,
    NTAG424DNA,
    NTAG424DNATT,
    UNKNOWN_TYPE
} nxp_cardtype_t;

typedef struct {
    bool Authenticated;
    uint8_t Key[16];
    uint8_t KeyNum;
    uint8_t RndA[16];
    uint8_t RndB[16];
    uint8_t TI[4];
    uint8_t PICCap2[6];
    uint8_t PCDCap2[6];
    uint8_t Kenc[16];
    uint8_t Kmac[16];
    uint16_t Cmd_Ctr;
} ntag424session_t;

typedef struct {
    uint8_t  key_number;
    uint8_t  file_id;
    uint8_t  read_access;
    uint8_t  read_write_access;
    uint8_t  write_access;
    uint8_t  change_access;
    uint8_t  SDMMetaRead;
    uint8_t  SDMFileRead;
    uint8_t  SDMCtrRet;
    ntag424_comm_mode_t comm_mode;
    uint16_t file_size;

} file_properties_t;

typedef enum ntag424_comm_mode {
    NTAG424_COMM_MODE_PLAIN = 0x00,
    NTAG424_COMM_MODE_MACED = 0x01,
    NTAG424_COMM_MODE_ENC = 0x03,
} ntag424_comm_mode_t;

// ntag424_get_version_res struct
typedef struct {
    uint8_t  versionHW[7];
    uint8_t  versionSW[7];
    uint8_t  details[14];
    uint8_t  uid[7];
    int      uid_len;
} ntag424_get_version_res;

static char *GetSDMMetaReadStr(uint8_t access_condition) {

    static char buf[40] = {0x00};
    char *retStr = buf;

    switch(access_condition) {
        case 0x00:
        case 0x01:
        case 0x02:
        case 0x03:
        case 0x04:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("Key 0x%02X used to encrypt PICCData") " )", access_condition, access_condition);
            break;
        case 0x0E:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("Plain PICCData mirroring") " )", access_condition);
            break;
        case 0x0F:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("No PICCData mirroring") " )", access_condition);
            break;
        default:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _RED_("Unknown") " )", access_condition);
            break;
    }

    return buf;
}

static char *GetSDMFileReadStr(uint8_t access_condition) {

    static char buf[40] = {0x00};
    char *retStr = buf;

    switch(access_condition) {
        case 0x00:
        case 0x01:
        case 0x02:
        case 0x03:
        case 0x04:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("Free access, key 0x%02X applied for SDM") " )", access_condition, access_condition);
            break;
        case 0x0E:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _YELLOW_("RFU") " )", access_condition);
            break;
        case 0x0F:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("No SDM for reading") " )", access_condition);
            break;
        default:
            snprintf(retStr, sizeof(buf), "0x%02X ( " _RED_("Unknown") " )", access_condition);
            break;
    }

    return buf;
}

//
// Original from  https://github.com/rfidhacking/node-sdm/
//
typedef struct {
    uint8_t  tag;
    uint8_t  uid[7];
    uint8_t  cnt[3];
    uint32_t cnt_int;
    uint8_t  uid_len;
} sdm_picc_t;

typedef struct {
    bool    uid_mirror;
    bool    cnt_mirror;
    uint8_t uid_len;
} picc_tag_t;

static picc_tag_t interpret_picc_tag(uint8_t tag) {
    picc_tag_t o = {0};
    o.uid_mirror = (tag & 0x80) >> 7;
    o.cnt_mirror = (tag & 0x40) >> 6;
    o.uid_len = o.uid_mirror ? tag & 0x0F : 0;

    return o;
}


static int NTAG424_AuthenticateEV2First(ntag424_get_version_res *res, ntag424session_t *session) {

    uint8_t cmd[16] = {0};
    uint8_t resp[16] = {0};
    uint8_t iv[16] = {0};
    uint8_t aesk [16] = {0};
    uint8_t aeskey[16] = {0};
    uint8_t PICCData[16] = {0};

    // 1. Generate AES key


    // 2. Encrypt AES key with AES-128-ECB using the key 0x00
    //    (the default key for the NTAG424DNx0EV2)
    //    and store the result in the AESK variable
    //    (AESK = AES-128-ECB(0x00, AESkey))
    memcpy(aesk, aeskey, 16);
    if (mbedtls_aes_setkey_enc(&aes_ctx, aeskey, 128) != 0) {
        PrintAndLogEx(ERR, "AES-128-ECB setkey_enc failed");
        return PM3_EFAILED;
    }

}

static int sdm_generator(void) {

    // NXP Secure Dynamic Messaging (SDM)  with Secure Unique NFC message (SUN)
    // Where do they come up with these names?
    //
    // ref:
    // https://www.nxp.com/docs/en/application-note/AN12196.pdf

    // SMD / CMAC
    uint8_t iv[16] = {0};
    uint8_t aeskey[16]  = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01};
    //uint8_t enc_txt[16] = {0xEF, 0x96, 0x3F, 0xF7, 0x82, 0x86, 0x58, 0xA5, 0x99, 0xF3, 0x04, 0x15, 0x10, 0x67, 0x1E, 0x88};
    uint8_t enc_txt[16] = {0x15, 0x12, 0xD1, 0x87, 0x9E, 0x5F, 0xAE, 0x5B, 0x90, 0x54, 0xFA, 0xAA, 0x94, 0xA2, 0xC6, 0xF4};
    uint8_t dec_txt[16] = {0};

    aes_decode(iv, aeskey, enc_txt, dec_txt, sizeof(enc_txt));

    PrintAndLogEx(INFO, "Ntag424 SUN message validation and encryption");
    PrintAndLogEx(INFO, "Enc text... %s", sprint_hex(enc_txt, sizeof(enc_txt)));
    PrintAndLogEx(INFO, "Dec text... %s", sprint_hex(dec_txt, sizeof(dec_txt)));

    sdm_picc_t o = {0};
    o.tag  = dec_txt[0];
    picc_tag_t t = interpret_picc_tag(o.tag);
    if(t.uid_mirror) {
        PrintAndLogEx(INFO, "UID is mirrored");
        PrintAndLogEx(INFO, "UID len.... %u", t.uid_len);
        o.uid_len = t.uid_len;
        memcpy(o.uid, dec_txt + 1, t.uid_len);
    }

    uint8_t cnt_offset = 1 + t.uid_len;

    if(t.cnt_mirror) {
        PrintAndLogEx(INFO, "CNT is mirrored");
        
        memcpy(o.cnt, dec_txt + cnt_offset, sizeof(o.cnt));
        o.cnt_int = MemLeToUint3byte(o.cnt);
    }

    PrintAndLogEx(INFO, "Decypted text");
    PrintAndLogEx(INFO, "  Tag........... 0x%02X", o.tag);
    if(t.uid_mirror) {
        PrintAndLogEx(INFO, "  UID........... %s", sprint_hex(o.uid, sizeof(o.uid)));
        PrintAndLogEx(INFO, "  Count bytes... %s", sprint_hex(o.cnt, sizeof(o.cnt)));
    }
    if(t.cnt_mirror) {
        PrintAndLogEx(INFO, "  Count value... 0x%X ( %u )", o.cnt_int, o.cnt_int);
    }

    // SV2 as per NXP DS465430 (NT4H2421Gx Data sheet)
    uint8_t sv2data[16] = {0x3C, 0xC3, 0x00, 0x01, 0x00, 0x80};

    if(t.uid_mirror) {
        memcpy(sv2data + 6, o.uid, o.uid_len);
    }
    if(t.cnt_mirror) {
        memcpy(sv2data + 6 + o.uid_len, o.cnt, sizeof(o.cnt));
    }

    uint8_t cmackey[16] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
    mbedtls_aes_cmac_prf_128(aeskey, 16, sv2data, sizeof(sv2data), cmackey);

    uint8_t zero[16] = {0};
    uint8_t full_cmac[16] = {0};
    mbedtls_aes_cmac_prf_128(cmackey, 16, zero, 0, full_cmac);

    uint8_t cmac[8] = {0};
    for (int i = 0, j = 1; i < 8; ++i, j += 2) {
        cmac[i] = full_cmac[j];
    }

    uint8_t veri[] = {0x9F, 0x90, 0xBC, 0xE9, 0xB8, 0x6F, 0xB2, 0x82};
    //uint8_t veri[] = {0x8B, 0x8D, 0x37, 0xC0, 0xAE, 0x6D, 0x8C, 0x8B};
    uint8_t is_ok = (memcmp(cmac, veri, 8) == 0);

    PrintAndLogEx(INFO, "SDM cmac... %s ( %s )",
                  sprint_hex(cmac, sizeof(cmac)),
                  (is_ok) ? _GREEN_("ok") : _RED_("fail")
                 );

    return PM3_SUCCESS;
}

static char *getCardSizeStr(uint8_t fsize) {

    static char buf[40] = {0x00};
    char *retStr = buf;

    uint16_t usize = 1 << (((uint16_t)fsize >> 1) + 1);
    uint16_t lsize = 1 << ((uint16_t)fsize >> 1);

    // is  LSB set?
    if (fsize & 1)
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("%d - %d bytes") " )", fsize, usize, lsize);
    else
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("%d bytes") " )", fsize, lsize);
    return buf;
}

static char *getProtocolStr(uint8_t id, bool hw) {

    static char buf[50] = {0x00};
    char *retStr = buf;

    if (id == 0x04) {
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("ISO 14443-3 MIFARE, 14443-4") " )", id);
    } else if (id == 0x05) {
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("ISO 14443-4") " )", id);
    } else {
        snprintf(retStr, sizeof(buf), "0x%02X ( " _YELLOW_("Unknown") " )", id);
    }
    return buf;
}

static char *getTypeStr(uint8_t type) {

    static char buf[40] = {0x00};
    char *retStr = buf;

    if (type == 0x04)
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("NTAG") " )", type);
    else
        snprintf(retStr, sizeof(buf), "0x%02X ( " _YELLOW_("Unknown") " )", type);
    return buf;
}

static char *getSubTypeStr(uint8_t type, uint8_t subtype) {

    static char buf[40] = {0x00};
    char *retStr = buf;

    if (type == 0x04 && subtype == 0x08)
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("50 pF") " )", subtype);
    else if (type == 0x04 && subtype == 0x02)
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("70 pF") " )", subtype);
    else
        snprintf(retStr, sizeof(buf), "0x%02X ( " _YELLOW_("Unknown") " )", subtype);
    return buf;
}

static char *getVendorInfo(uint8_t vendor) {

    static char buf[40] = {0x00};
    char *retStr = buf;

    if (vendor == 0x04)
        snprintf(retStr, sizeof(buf), "0x%02X ( " _GREEN_("NXP") " )", vendor);
    else
        snprintf(retStr, sizeof(buf), "0x%02X ( " _YELLOW_("Unknown") " )", vendor);

    return buf;
}

static nxp_cardtype_t getCardType(ntag424_get_version_res *info) {

    if (info->versionHW[0] == 0x04){
        if (info->versionHW[1] == 0x04) {
            if(info->versionHW[3] == 0x10) {
                return NTAG413DNA;
            } else if (info->versionHW[3] == 0x30) {
                uint8_t subver = info->versionHW[2] & 0xF;
                if(subver == 0x2)
                    return NTAG424DNA;
                else if(subver == 0x8)
                    return NTAG424DNATT;
            }
        }
    }
    return UNKNOWN_TYPE;
    
}


static const char *getProductTypeStr(nxp_cardtype_t cardype) {

    switch(cardype)
    {
        case NTAG413DNA:
            return "NTAG 413 DNA";
            break;
        case NTAG424DNA:
            return "NTAG 424 DNA";
            break;
        case NTAG424DNATT:
            return "NTAG 424 DNA TT";
            break;
        case UNKNOWN_TYPE:
        default:
            return "Unknown";
            break;
    }
}

static int ntag424_get_info(ntag424_get_version_res *info) {
        // Check if the tag reponds to APDUs.
    uint8_t response[20];
    int response_len = 0;

    uint8_t aGET_VER[80];
    int aGET_VER_n = 0;
    param_gethex_to_eol("9060000000", 0, aGET_VER, sizeof(aGET_VER), &aGET_VER_n);
    int res = ExchangeAPDU14a(aGET_VER, aGET_VER_n, true, true, response, sizeof(response), &response_len);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(FAILED, "Tag did not respond to GetVersion part 1 APDU. Aborting...");
        return res;
    }else {
        PrintAndLogEx(SUCCESS, "GetVersion part 1 APDU Response: %s", sprint_hex_inrow(response, response_len));
    }

    memcpy(info->versionHW, response, 7);
    
    uint8_t aGET_VER_TWO[80];
    int aGET_VER_TWO_n = 0;
    param_gethex_to_eol("90AF000000", 0, aGET_VER_TWO, sizeof(aGET_VER_TWO), &aGET_VER_TWO_n);
    res = ExchangeAPDU14a(aGET_VER_TWO, aGET_VER_TWO_n, false, true, response, sizeof(response), &response_len);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(FAILED, "Tag did not respond to GetVersion part 2 APDU. Aborting...");
        return res;
    }else {
        PrintAndLogEx(SUCCESS, "GetVersion part 2 APDU Response: %s", sprint_hex_inrow(response, response_len));
    }

    memcpy(info->versionSW, response, 7);

    uint8_t aGET_VER_THREE[80];
    int aGET_VER_THREE_n = 0;
    param_gethex_to_eol("90AF000000", 0, aGET_VER_THREE, sizeof(aGET_VER_THREE), &aGET_VER_THREE_n);
    res = ExchangeAPDU14a(aGET_VER_THREE, aGET_VER_THREE_n, false, false, response, sizeof(response), &response_len);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(FAILED, "Tag did not respond to GetVersion part 3 APDU. Aborting...");
        return res;
    }else {
        PrintAndLogEx(SUCCESS, "GetVersion part 3 APDU Response: %s", sprint_hex_inrow(response, response_len));
    }
    memcpy(info->details, response, 14);

    memcpy(info->uid, response, 7);

    info->uid_len = 7;

    return PM3_SUCCESS;
}

static int CmdHF_ntag424_view(const char *Cmd) {

    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf ntag424 view",
                  "Print a NTAG 424 DNA dump file (bin/eml/json)",
                  "hf ntag424 view -f hf-ntag424-01020304-dump.bin"
                 );
    void *argtable[] = {
        arg_param_begin,
        arg_str1("f", "file", "<fn>", "Filename of dump"),
        arg_lit0("v", "verbose", "Verbose output"),
        arg_param_end
    };
    CLIExecWithReturn(ctx, Cmd, argtable, false);
    int fnlen = 0;
    char filename[FILE_PATH_SIZE];
    CLIParamStrToBuf(arg_get_str(ctx, 1), (uint8_t *)filename, FILE_PATH_SIZE, &fnlen);
    bool verbose = arg_get_lit(ctx, 2);
    CLIParserFree(ctx);

    // read dump file
    uint8_t *dump = NULL;
    size_t bytes_read = NTAG424_MAX_BYTES;
    int res = pm3_load_dump(filename, (void **)&dump, &bytes_read, NTAG424_MAX_BYTES);
    if (res != PM3_SUCCESS) {
        return res;
    }

    if (verbose) {
        PrintAndLogEx(INFO, "File: " _YELLOW_("%s"), filename);
        PrintAndLogEx(INFO, "File size %zu bytes", bytes_read);
    }

    free(dump);
    return PM3_SUCCESS;
}

static int CmdHF_ntag424_sdm(const char *Cmd) {

    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf ntag424 sdm",
                  "Validate a SDM message",
                  "hf ntag424 sdm"
                 );
    void *argtable[] = {
        arg_param_begin,
        arg_param_end
    };
    CLIExecWithReturn(ctx, Cmd, argtable, false);
    CLIParserFree(ctx);

    return sdm_generator();
}

static int ntag424_select_tag(void) {
    uint8_t response[20];
    int response_len = 0;

    uint8_t aSELECT[80];
    int aSELECT_n = 0;

    param_gethex_to_eol("93FE000000", 0, aSELECT, sizeof(aSELECT), &aSELECT_n);
    int res = ExchangeAPDU14a(aSELECT, aSELECT_n, true, true, response, sizeof(response), &response_len);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(FAILED, "Tag did not respond to Select APDU. Aborting...");
        return res;
    }else {
        PrintAndLogEx(SUCCESS, "Select APDU Response: %s", sprint_hex_inrow(response, response_len));
    }

    return PM3_SUCCESS;
}

static int ntag424_select_and_auth(uint8_t *key) {
    int res = ntag424_select_tag();
    if (res != PM3_SUCCESS) {
        return res;
    }

    uint8_t response[20];
    int response_len = 0;

    uint8_t aAUTH[80];
    int aAUTH_n = 0;
    param_gethex_to_eol("90AF000000", 0, aAUTH, sizeof(aAUTH), &aAUTH_n);
    res = ExchangeAPDU14a(aAUTH, aAUTH_n, false, true, response, sizeof(response), &response_len);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(FAILED, "Tag did not respond to Authenticate APDU. Aborting...");
        return res;
    }else {
        PrintAndLogEx(SUCCESS, "Authenticate APDU Response: %s", sprint_hex_inrow(response, response_len));
    }

    return PM3_SUCCESS;
}

static int ntag_424_read_ndef(uint8_t *key, uint8_t *ndef, size_t *ndef_len) {
    int res = ntag424_select_and_auth(key);
    if (res != PM3_SUCCESS) {
        return res;
    }

    uint8_t response[20];
    int response_len = 0;

    uint8_t aREAD[80];
    int aREAD_n = 0;
    param_gethex_to_eol("90F50000010200", 0, aREAD, sizeof(aREAD), &aREAD_n);
    res = ExchangeAPDU14a(aREAD, aREAD_n, false, false, response, sizeof(response), &response_len);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(FAILED, "Tag did not respond to Read NDEF APDU. Aborting...");
        return res;
    }else {
        PrintAndLogEx(SUCCESS, "Read NDEF APDU Response: %s", sprint_hex_inrow(response, response_len));
    }

    memcpy(ndef, response, response_len);
    *ndef_len = response_len;

    return PM3_SUCCESS;
}


static int CmdHF_ntag424_ndefread(const char *Cmd) {
    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf ntag424 ndefread",
                    "Get info about NXP NTAG424 DNA Family styled tag.",
                    "hf ntag424 ndefread"
                    "hf ntag424 ndefread -k ffffffffffffffff -> read NDEF data using key\n"
                    "hf ntag424 ndefread -f myfilename -> save NDEF to file"
                    );
    void *argtable[] = {
        arg_param_begin,
        arg_lit0("v", "verbose", "Verbose output"),
        arg_str0("k", "key", "<hex>", "Key to use for reading NDEF file (16 hex bytes)"),
        arg_str0("f", "file", "<fn>", "Save raw NDEF to file"),
        arg_param_end
    };
    CLIExecWithReturn(ctx, Cmd, argtable, true);

    bool verbose = arg_get_lit(ctx, 1);
    uint8_t key[16] = {0};
    int keylen = 0;
    CLIGetHexWithReturn(ctx, 2, key, &keylen);
    uint8_t filename[FILE_PATH_SIZE] = {0};
    int fnlen = 0;
    CLIParamStrToBuf(arg_get_str(ctx, 3), (uint8_t *)filename, FILE_PATH_SIZE, &fnlen);

    CLIParserFree(ctx);

    //uint8_t response[PM3_CMD_DATA_SIZE] = {0};
    //size_t response_len = 0;

    ntag424_get_version_res info;
    int res = ntag424_get_info(&info);
    if (res != PM3_SUCCESS) {
        return res;
    }
    
    nxp_cardtype_t cardtype = getCardType(&info);
    if(cardtype != NTAG424DNA && cardtype != NTAG424DNATT && cardtype != NTAG413DNA) {
        PrintAndLogEx(ERR, "This command is only for NTAG424 DNA Family styled tags.");
        return PM3_EINVARG;
    }
   

   
    //res = ntag424_select_auth(&info, key, keylen);

    if (res != PM3_SUCCESS) {
        return res;
    }


    
    PrintAndLogEx(INFO, "Reading NDEF file");

    

    if(verbose) {
        
    }

    if (keylen > 0) {
        if (keylen != 16) {
            PrintAndLogEx(ERR, "Key must be 16 hex bytes");
            return PM3_EINVARG;
        }
        PrintAndLogEx(INFO, "Using key: %s", sprint_hex(key, 16));
    }
    
    return PM3_SUCCESS;
}

static int CmdHF_ntag424_info(const char *Cmd) {

    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf ntag424 info",
                  "Get info about NXP NTAG424 DNA Family styled tag",
                  "hf ntag424 info"
                 );
    void *argtable[] = {
        arg_param_begin,
        arg_param_end
    };
    CLIExecWithReturn(ctx, Cmd, argtable, true);
    CLIParserFree(ctx);

    PrintAndLogEx(INFO, "not implemented yet");
    PrintAndLogEx(INFO, "Feel free to contribute!");

    // has hardcoded application and three files.
    uint8_t rats[] = { 0xE0, 0x80 }; 
    PacketResponseNG resp;
    clearCommandBuffer();
    SendCommandMIX(CMD_HF_ISO14443A_READER, ISO14A_RAW | ISO14A_APPEND_CRC | ISO14A_NO_DISCONNECT, 2, 0, rats, sizeof(rats));
    WaitForResponse(CMD_ACK, &resp);

    ntag424_get_version_res info;
    int res = ntag424_get_info(&info);
    if (res != PM3_SUCCESS) {
        DropField();
        return res;
    }

    nxp_cardtype_t cardtype = getCardType(&info);
    if (cardtype == UNKNOWN_TYPE) {
        PrintAndLogEx(INFO, "Card doesn't seem to be in the NXP NTAG424 DNA Family");
        DropField();
        return PM3_SUCCESS;
    }

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "---------------------------------- " _CYAN_("Tag Information") " ----------------------------------");
    PrintAndLogEx(SUCCESS, "              UID: " _GREEN_("%s"), sprint_hex(info.uid, info.uid_len));
    PrintAndLogEx(SUCCESS, "     Batch number: " _GREEN_("%s"), sprint_hex(info.details + 7, 5));
    PrintAndLogEx(SUCCESS, "  Production date: week " _GREEN_("%02x") " / " _GREEN_("20%02x"), info.details[12], info.details[13]);


    PrintAndLogEx(SUCCESS, "     Product type: " _GREEN_("%s"), getProductTypeStr(cardtype));
    

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "--- " _CYAN_("Hardware Information"));
    PrintAndLogEx(INFO, "   raw: %s", sprint_hex_inrow(info.versionHW, sizeof(info.versionHW)));

    PrintAndLogEx(INFO, "     Vendor Id: %s", getVendorInfo(info.versionHW[0]));
    PrintAndLogEx(INFO, "          Type: %s", getTypeStr(info.versionHW[1]));
    PrintAndLogEx(INFO, "       Subtype: %s", getSubTypeStr(info.versionHW[1], info.versionHW[2]));
    PrintAndLogEx(INFO, "       Version: " _YELLOW_("%x.%x"),  info.versionHW[3], info.versionHW[4]);
    PrintAndLogEx(INFO, "  Storage size: %s", getCardSizeStr(info.versionHW[5]));
    PrintAndLogEx(INFO, "      Protocol: %s", getProtocolStr(info.versionHW[6], true));
    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "--- " _CYAN_("Software Information"));
    PrintAndLogEx(INFO, "   raw: %s", sprint_hex_inrow(info.versionSW, sizeof(info.versionSW)));
    PrintAndLogEx(INFO, "     Vendor Id: " _YELLOW_("%s"), getVendorInfo(info.versionSW[0]));
    PrintAndLogEx(INFO, "          Type: " _YELLOW_("0x%02X"), info.versionSW[1]);
    PrintAndLogEx(INFO, "       Subtype: " _YELLOW_("0x%02X"), info.versionSW[2]);
    PrintAndLogEx(INFO, "       Version: " _YELLOW_("%x.%x"),  info.versionSW[3], info.versionSW[4]);
    PrintAndLogEx(INFO, "  Storage size: %s", getCardSizeStr(info.versionSW[5]));
    PrintAndLogEx(INFO, "      Protocol: %s", getProtocolStr(info.versionSW[6], false));
    PrintAndLogEx(NORMAL, "");
  
    sdm_generator();

    DropField();

    return PM3_SUCCESS;
}



//------------------------------------
// Menu Stuff
//------------------------------------
static command_t CommandTable[] = {
    {"help",        CmdHelp,                    AlwaysAvailable,  "This help"},
    {"-----------", CmdHelp,                    IfPm3Iso14443a,   "----------------------- " _CYAN_("operations") " -----------------------"},
    {"info",        CmdHF_ntag424_info,         IfPm3Iso14443a,   "Tag information"},
    {"ndefread", CmdHF_ntag424_sdm,             IfPm3Iso14443a,   "Not implemented"},
    {"ndefread",    CmdHF_ntag424_ndefread,     IfPm3Iso14443a,   "Prints NDEF records from card"},
    {"view",        CmdHF_ntag424_view,         AlwaysAvailable,  "Display content from tag dump file"},
    {NULL, NULL, NULL, NULL}
};

static int CmdHelp(const char *Cmd) {
    (void)Cmd; // Cmd is not used so far
    CmdsHelp(CommandTable);
    return PM3_SUCCESS;
}

int CmdHF_ntag424(const char *Cmd) {
    clearCommandBuffer();
    return CmdsParse(CommandTable, Cmd);
}
