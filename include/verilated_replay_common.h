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
/// \brief Verilator: Include for common replay code
///
///     See verilator_replay
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#ifndef _VERILATED_REPLAY_COMMON_H_
#define _VERILATED_REPLAY_COMMON_H_ 1  ///< Header Guard

#include "verilated.h"
#include "gtkwave/fstapi.h"
#include <string>
#include <map>

class VerilatedReplayCommon {
public:
    struct fstVar {
        // Can't just save the struct fstHier* that fstReadIterateHier()
        // gives us because it recycles that pointer
        struct fstHier hier;
        std::string fullName;
        fstVar(struct fstHier* _hierp, std::string _fullName):
            hier(*_hierp), fullName(_fullName) {}
        fstVar() {}
    };
    typedef std::map<fstHandle, fstVar> VarMap;
protected:
    void* m_fstp;
    VarMap m_inputs;
    VarMap m_outputs;
public:
    VerilatedReplayCommon() {}
    ~VerilatedReplayCommon() {}
    void openFst(const std::string& fstName);
    void search(std::string targetScope);
};

#endif  // Guard
