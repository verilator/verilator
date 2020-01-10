#include "VlrGenerator.h"
#include "V3Error.h"
#include "gtkwave/fstapi.h"

// TODO -- can we not do this?
// Include the GTKWave implementation directly
#define FST_CONFIG_INCLUDE "fst_config.h"
#include "gtkwave/fastlz.c"
#include "gtkwave/fstapi.c"
// TODO -- use the system's LZ4 library, not this copy
#include "gtkwave/lz4.c"

void VlrGenerator::getFstIO() {
    void* fst = fstReaderOpen(opts().fst());
    const char* scope = "";
    string targetScope;
    if (m_opts.scope()) targetScope = string(m_opts.scope());

    while (struct fstHier* hier = fstReaderIterateHier(fst)) {
        if (hier->htyp == FST_HT_SCOPE) {
            scope = fstReaderPushScope(fst, hier->u.scope.name, NULL);
            if (targetScope.empty()) targetScope = string(scope);
            UINFO(3, "SCOPE "<<scope<<endl);
        } else if (hier->htyp == FST_HT_UPSCOPE) {
            scope = fstReaderPopScope(fst);
            UINFO(3, "UPSCOPE "<<scope<<endl);
        } else if (hier->htyp == FST_HT_VAR) {
            if (string(scope) == targetScope) {
                string varName = string(scope) + "." + string(hier->u.var.name);
                switch (hier->u.var.direction) {
                    case FST_VD_INPUT:
                        UINFO(3, "VAR input "<<hier->u.var.name<<endl);
                        m_inputs.push_back(varName);
                        break;
                    case FST_VD_OUTPUT:
                        UINFO(3, "VAR output "<<hier->u.var.name<<endl);
                        m_outputs.push_back(varName);
                        break;
                    default: break;
                }
            }
        }
    }
}

void VlrGenerator::emitVltCode() {
}
