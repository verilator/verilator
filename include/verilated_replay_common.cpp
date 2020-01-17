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
#include <iostream>

using namespace std;

// TODO -- can we not do this?
// Include the GTKWave implementation directly
// Ugh, building with verilated_fst_c.cpp, brings this in, let's really not do this
//#define FST_CONFIG_INCLUDE "fst_config.h"
//#include "gtkwave/fastlz.c"
//#include "gtkwave/fstapi.c"
//// TODO -- use the system's LZ4 library, not this copy
//#include "gtkwave/lz4.c"

void VerilatedReplayCommon::openFst(const string& fstName) {
    m_fstp = fstReaderOpen(fstName.c_str());
    if (!m_fstp) {
        // TODO -- a better way to fatal in either Verilator or in the runtime?
        cout<<"Could not open FST: "<<fstName<<endl;
        exit(-1);
    }
}

void VerilatedReplayCommon::searchFst(const string& targetScope) {
    const char* scope = "";
    string searchScope(targetScope);

    while (fstHier* hierp = fstReaderIterateHier(m_fstp)) {
        if (hierp->htyp == FST_HT_SCOPE) {
            scope = fstReaderPushScope(m_fstp, hierp->u.scope.name, NULL);
            if (searchScope.empty()) searchScope = string(scope);
        } else if (hierp->htyp == FST_HT_UPSCOPE) {
            scope = fstReaderPopScope(m_fstp);
        } else if (hierp->htyp == FST_HT_VAR) {
            if (string(scope) == searchScope) {
                string varName = string(scope) + "." + string(hierp->u.var.name);
                switch (hierp->u.var.direction) {
                    case FST_VD_INPUT:
                        m_inputs[hierp->u.var.handle] =
                            fstVar(hierp, varName);
                        break;
                    case FST_VD_OUTPUT:
                        m_outputs[hierp->u.var.handle] =
                            fstVar(hierp, varName);
                        break;
                    default: break;
                }
            }
        }
    }
}
