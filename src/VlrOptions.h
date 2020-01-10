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

#include <string>

class VlrOptions {
public:
    // CONSTRUCTORS
    VlrOptions():
        m_fst(NULL), m_scope(NULL), m_vlt(false)
    {}
    ~VlrOptions() {}

    // METHODS
    void parseOptsList(int argc, char** argv);

    const char* fst() { return m_fst; }
    const char* scope() { return m_scope; }
    bool vlt() { return m_vlt; }
private:
    void showVersion(bool version);
    std::string version();
    bool onoff(const char* sw, const char* arg, bool& flag);

    const char* m_fst;
    const char* m_scope;
    bool m_vlt;
};

#endif  // guard
