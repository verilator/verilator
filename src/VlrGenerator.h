// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_replay: Replay code generator
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

#ifndef _VLRGENERATOR_H_
#define _VLRGENERATOR_H_ 1

#include "VlrOptions.h"
#include "verilated_replay_common.h"
#include <list>

class VlrGenerator: public VerilatedReplayCommon {
public:
    // CONSTRUCTORS
    // TODO -- passing this in the constructor is wonky, but we'd need VlrOptions to
    // inherit from VerilatedReplayCommon (or something) to avoid this, but that
    // would break the foo.opt.bar() convention in Verilator if VlrGenerator
    // further inherited from VlrOptions
    VlrGenerator(): m_opts(this) {}
    ~VlrGenerator() {}

    // METHODS
    VlrOptions& opts() { return m_opts; }
    void searchFst();
    std::string replayName(const std::string& fullName);
    void emitVltCode();
private:
    typedef std::list<std::string> StrList;

    VlrOptions m_opts;
};

#endif  // guard
