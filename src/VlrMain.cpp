// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_replay: main()
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

#include "VlrGenerator.h"
#include "V3Error.h"

int main(int argc, char** argv) {
    VlrGenerator gen;

    // Parse command line options
    gen.opts().parseOptsList(argc-1, argv+1);

    // Read signals from FST or signals file
    if (gen.opts().fst()) {
        gen.getFstIO();
    }
    // TODO -- manually specified lists
    // TODO -- check for none of the above

    // Emit replay code
    if (gen.opts().vlt()) {
        gen.emitVltCode();
    }
    // TODO -- DPI and/or VPI wrappers
    // TODO -- check no emitters
}
