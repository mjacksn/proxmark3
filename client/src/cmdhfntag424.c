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
    NTAG413DNA,
    NTAG424DNA,
    NTAG424DNATT,
    UNKNOWN_TYPE
} nxp_cardtype_t;

typedef struct ntag424_get_version_res {
    uint8_t isOK;
    uint8_t uid[7];
    uint8_t uidlen;
    uint8_t versionHW[7];
    uint8_t versionSW[7];
    uint8_t details[14];
} PACKED ntag424_get_version_res;

//
// Original from  https://github.com/rfidhacking/node-sdm/
//
typedef struct sdm_picc_s {
    uint8_t tag;
    uint8_t uid[7];
    uint8_t cnt[3];
    uint32_t cnt_int;
} sdm_picc_t;

static int sdm_generator(void) {

    // NXP Secure Dynamic Messaging (SDM)  with Secure Unique NFC message (SUN)
    // Where do they come up with these names?
    //
    // ref:
    // https://www.nxp.com/docs/en/application-note/AN12196.pdf

    // SMD / CMAC
    uint8_t iv[16] = {0};
    uint8_t aeskey[16]  = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
    // uint8_t enc_txt[16] = {0xEF, 0x96, 0x3F, 0xF7, 0x82, 0x86, 0x58, 0xA5, 0x99, 0xF3, 0x04, 0x15, 0x10, 0x67, 0x1E, 0x88};
    uint8_t enc_txt[16] = {0xe6, 0x45, 0xb6, 0x15, 0x4e, 0x8f, 0x32, 0x7d, 0xfb, 0xab, 0x93, 0x4d, 0x4c, 0x66, 0x46, 0x14};
    uint8_t dec_txt[16] = {0};

    aes_decode(iv, aeskey, enc_txt, dec_txt, sizeof(enc_txt));

    PrintAndLogEx(INFO, "Ntag424 SUN message validation and encryption");
    PrintAndLogEx(INFO, "Enc text... %s", sprint_hex(enc_txt, sizeof(enc_txt)));
    PrintAndLogEx(INFO, "Dec text... %s", sprint_hex(dec_txt, sizeof(dec_txt)));

    sdm_picc_t o = {0};
    o.tag  = dec_txt[0];
    memcpy(o.uid, dec_txt + 1, sizeof(o.uid));
    memcpy(o.cnt, dec_txt + 8, sizeof(o.cnt));
    o.cnt_int = MemLeToUint3byte(o.cnt);

    PrintAndLogEx(INFO, "Decypted text");
    PrintAndLogEx(INFO, "  Tag........... 0x%02X", o.tag);
    PrintAndLogEx(INFO, "  UID........... %s", sprint_hex(o.uid, sizeof(o.uid)));
    PrintAndLogEx(INFO, "  Count bytes... %s", sprint_hex(o.cnt, sizeof(o.cnt)));
    PrintAndLogEx(INFO, "  Count value... 0x%X ( %u )", o.cnt_int, o.cnt_int);

    // SV2 as per NXP DS465430 (NT4H2421Gx Data sheet)
    uint8_t sv2data[16] = {0x3C, 0xC3, 0x00, 0x01, 0x00, 0x80};

    memcpy(sv2data + 6, o.uid, sizeof(o.uid));
    memcpy(sv2data + 6 + sizeof(o.uid), o.cnt, sizeof(o.cnt));

    uint8_t cmackey[16] = {0};
    mbedtls_aes_cmac_prf_128(aeskey, 16, sv2data, sizeof(sv2data), cmackey);

    uint8_t zero[16] = {0};
    uint8_t full_cmac[16] = {0};
    mbedtls_aes_cmac_prf_128(cmackey, 16, zero, 0, full_cmac);

    uint8_t cmac[8] = {0};
    for (int i = 0, j = 1; i < 8; ++i, j += 2) {
        cmac[i] = full_cmac[j];
    }

    //uint8_t veri[] = {0x94, 0xee, 0xd9, 0xee, 0x65, 0x33, 0x70, 0x86};
    uint8_t veri[] = {0x8b, 0xa1, 0xfb, 0x47, 0x0d, 0x63, 0x39, 0xe8 };
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

    info->uidlen = 7;

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

static int CmdHF_ntag424_info(const char *Cmd) {

    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf ntag424 info",
                  "Get info about NXP NTAG424 DNA Family styled tag.",
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
        PrintAndLogEx(INFO, "Card doesnt seem to be an NTAG 424");
        DropField();
        return PM3_SUCCESS;
    }

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "---------------------------------- " _CYAN_("Tag Information") " ----------------------------------");
    PrintAndLogEx(SUCCESS, "              UID: " _GREEN_("%s"), sprint_hex(info.uid, info.uidlen));
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
  

    DropField();

    return PM3_SUCCESS;
}

//------------------------------------
// Menu Stuff
//------------------------------------
static command_t CommandTable[] = {
    {"help",     CmdHelp,                AlwaysAvailable,  "This help"},
    {"-----------", CmdHelp,             IfPm3Iso14443a,   "----------------------- " _CYAN_("operations") " -----------------------"},
    {"info",     CmdHF_ntag424_info,     IfPm3Iso14443a,   "Tag information"},
//     {"ndefread", CmdHF_ntag424_sdm,      IfPm3Iso14443a,   "Prints NDEF records from card"},
    {"sdm",      CmdHF_ntag424_sdm,      IfPm3Iso14443a,   "Prints NDEF records from card"},
    {"view",     CmdHF_ntag424_view,     AlwaysAvailable,  "Display content from tag dump file"},
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
