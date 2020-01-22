// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_replay: Command line options
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2020 by Todd Strader.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _VLROPTIONS_H_
#define _VLROPTIONS_H_ 1

#include "verilated_replay_common.h"
#include <string>

class VlrOptions {
public:
    // CONSTRUCTORS
    VlrOptions(VerilatedReplayCommon* replayp):
        m_checkOutputs(false), m_fst(NULL), m_replayTop(NULL), m_scope(NULL),
        m_vlt(false), m_replayp(replayp)
    {}
    ~VlrOptions() {}

    // METHODS
    void parseOptsList(int argc, char** argv);

    bool checkOutputs() { return m_checkOutputs; }
    const char* fst() { return m_fst; }
    const char* replayTop() { return m_replayTop; }
    const char* scope() { return m_scope; }
    bool vlt() { return m_vlt; }
private:
    void showVersion(bool version);
    std::string version();
    bool onoff(const char* sw, const char* arg, bool& flag);
    void readSignalList(const char* filename);
    void outputCheck();

    bool m_checkOutputs;
    char* m_fst;
    char* m_replayTop;
    char* m_scope;
    bool m_vlt;
    VerilatedReplayCommon* m_replayp;
};

#endif  // guard
