// DESCRIPTION: Verilator: Verilog Test module
//
// A test case for parameterized module.
//
// When a module is instantiatied with parameter, there will be two modules in
// the tree and eventually one will be removed after param and deadifyModules.
//
// This test is to check that the removal of dead module will not cause
// compilation error. Possible error was/is seen as:
//
// pure virtual method called
// terminate called without an active exception
// %Error: Verilator aborted.  Consider trying --debug --gdbbt
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jie Xu.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   wire [71:0] ctrl;
   wire [7:0] cl;                       // this line is added 

   memory #(.words(72)) i_memory (.clk (clk));

   assign ctrl = i_memory.mem[0];
   assign cl   = i_memory.mem[0][7:0];  // and this line
endmodule


// memory module, which is used with parameter
module memory (clk);
   input clk;

   parameter words = 16384, bits = 72;

   reg [bits-1 :0] mem[words-1 : 0];

endmodule
