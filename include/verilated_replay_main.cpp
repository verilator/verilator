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
/// \brief Verilator: Main used by verilator_replay
///
///     This utility will replay trace files onto a verilated design.
///     It is inteded to be used in conjunction with verilator_replay.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#include "verilated_replay.h"

double simTime = 0;
double sc_time_stamp() {
    return simTime;
}

// TODO -- should we make eval, final and trace(?) part of VerilatedModule?
// TODO -- generate this part
//#include "Vt_case_reducer.h"
//Vt_case_reducer* dutp = NULL;
//VerilatedVcdC* tfp = NULL;
//void VerilatedReplay::eval() {
//    dutp->eval();
//}
//
//void VerilatedReplay::trace() {
//#if VM_TRACE
//    if (tfp) tfp->dump(simTime);
//#endif  // VM_TRACE
//}
//
//void VerilatedReplay::final() {
//    dutp->final();
//}

int main(int argc, char** argv) {
    // TODO -- actual arg parsing
    std::string fstFilename(argv[1]);
    std::string scope(argv[2]);
    VL_PRINTF("FST = %s\n", fstFilename.c_str());
    VL_PRINTF("Scope = %s\n", scope.c_str());

    VerilatedReplay replay(fstFilename, simTime);
    if (replay.init(scope)) exit(-1);

//#if VM_TRACE
//    Verilated::traceEverOn(true);
//    tfp = new VerilatedFstC;
//    dutp->trace(tfp, 99);
//    tfp->open("replay.fst");
//    if (tfp) tfp->dump(simTime);
//#endif  // VM_TRACE

    if (replay.replay()) exit(-1);

//#if VM_TRACE
//    if (tfp) tfp->close();
//#endif  // VM_TRACE

    return 0;
}
