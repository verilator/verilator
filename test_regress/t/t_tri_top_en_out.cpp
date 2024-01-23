#include "verilated.h"
#include "Vt_tri_top_en_out.h"
#include <stdio.h>

//======================

int main(int argc, char** argv, char**) {
  // Setup context, defaults, and parse command line
  Verilated::debug(0);
  const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
  contextp->commandArgs(argc, argv);
  
  // Construct the Verilated model, from Vtop.h generated from Verilating
  const std::unique_ptr<Vt_tri_top_en_out> topp{new Vt_tri_top_en_out{contextp.get()}};

  // Initial input
  topp->drv_en = 1;
  topp->single_bit_io = 0;
  topp->bidir_single_bit_io = 0;
  topp->bus_64_io = 0;
  topp->bidir_bus_64_io = 0;
  topp->bus_128_io[0] = 0;
  topp->bus_128_io[1] = 0;
  topp->bus_128_io[2] = 0;
  topp->bus_128_io[3] = 0;
  topp->bidir_bus_128_io[0] = 0;
  topp->bidir_bus_128_io[1] = 0;
  topp->bidir_bus_128_io[2] = 0;
  topp->bidir_bus_128_io[3] = 0;
  topp->sub_io = 0;

  // Simulate until $finish
  while (!contextp->gotFinish()) {
    // Evaluate model
    topp->eval();

    // Advance time (to scheduled events)
    if (!topp->eventsPending()) break;
    contextp->time(topp->nextTimeSlot());

    printf("bidir_single_bit_io__en = %x\n", topp->bidir_single_bit_io__en);
    printf("bidir_bus_64_io__en = %x\n", (unsigned int)topp->bidir_bus_64_io__en);
    printf("bidir_bus_128_io__en = %x,%x,%x,%x\n",
	   topp->bidir_bus_128_io[3],
	   topp->bidir_bus_128_io[2],
	   topp->bidir_bus_128_io[1],
	   topp->bidir_bus_128_io[0]);
    printf("sub_io__en = %x\n", topp->sub_io__en);

    printf("bidir_single_bit_io = \n%x", topp->bidir_single_bit_io__out);
    printf("bidir_bus_64_io = \n%x", (unsigned int)topp->bidir_bus_64_io__out);
    printf("bidir_bus_128_io = %x,%x,%x,%x\n",
	   topp->bidir_bus_128_io__out[3],
	   topp->bidir_bus_128_io__out[2],
	   topp->bidir_bus_128_io__out[1],
	   topp->bidir_bus_128_io__out[0]);
    printf("sub_io = %x\n", topp->sub_io__out);
  }
  
  if (!contextp->gotFinish()) {
    printf("Exiting without $finish; no events left, time was %ld\n",
	   contextp->time());
    puts("final next:");
  }
  
  // Final model cleanup
  topp->final();
  return 0;
}
