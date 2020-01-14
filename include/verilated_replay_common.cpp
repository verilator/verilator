// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2020 by Todd Strader. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: Common replay code
///
///     See verilator_replay
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#include "verilated_replay_common.h"

using namespace std;

// TODO -- can we not do this?
// Include the GTKWave implementation directly
#define FST_CONFIG_INCLUDE "fst_config.h"
#include "gtkwave/fastlz.c"
#include "gtkwave/fstapi.c"
// TODO -- use the system's LZ4 library, not this copy
#include "gtkwave/lz4.c"

void VerilatedReplayCommon::openFst(const string& fstName) {
    m_fstp = fstReaderOpen(fstName.c_str());
    if (!m_fstp) {
        // TODO -- Verilator runtime way of tossing a fatal error?, see elsewhere
        VL_PRINTF("Could not open FST: %s\n", fstName.c_str());
        exit(-1);
    }
}

void VerilatedReplayCommon::search(string targetScope) {
    const char* scope = "";

    while (fstHier* hierp = fstReaderIterateHier(m_fstp)) {
        if (hierp->htyp == FST_HT_SCOPE) {
            scope = fstReaderPushScope(m_fstp, hierp->u.scope.name, NULL);
            if (targetScope.empty()) targetScope = string(scope);
        } else if (hierp->htyp == FST_HT_UPSCOPE) {
            scope = fstReaderPopScope(m_fstp);
        } else if (hierp->htyp == FST_HT_VAR) {
            if (string(scope) == targetScope) {
                string varName = string(scope) + "." + string(hierp->u.var.name);
                switch (hierp->u.var.direction) {
                    case FST_VD_INPUT:
                        m_inputs.push_back(fstVar(hierp, varName));
                        break;
                    case FST_VD_OUTPUT:
                        m_outputs.push_back(fstVar(hierp, varName));
                        break;
                    default: break;
                }
            }
        }
    }
}
