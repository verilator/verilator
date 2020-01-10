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
/// \brief Verilator: Include for replay tool
///
///     See verilator_replay
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#ifndef _VERILATED_REPLAY_H_
#define _VERILATED_REPLAY_H_ 1  ///< Header Guard

#include "verilated.h"
#include "gtkwave/fstapi.h"
#include <string>

class VerilatedReplay {
private:
    void createMod();
    void eval();
    void trace();
    void final();
    void fstCb(uint64_t time, fstHandle facidx, const unsigned char* value,
               uint32_t len);
    static void fstCallback(void* userData, uint64_t time, fstHandle facidx,
                            const unsigned char* value);
    static void fstCallbackVarlen(void* userData, uint64_t time, fstHandle facidx,
                                  const unsigned char* value, uint32_t len);

    std::string m_fstName;
    double& m_simTime;
    VerilatedModule* m_modp;
    void* m_fstp;
    uint64_t m_time;
public:
    VerilatedReplay(const std::string& fstName, double& simTime):
        m_fstName(fstName), m_simTime(simTime)
    {}
    ~VerilatedReplay();
    int init();
    int replay();
};

#endif  // Guard
