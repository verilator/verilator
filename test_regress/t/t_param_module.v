// DESCRIPTION: Verilator: Verilog Test module
//
// This test case is used for testing a modeule parameterized with a typed
// localparam.
//
// We find Verilator appears to mis-evaluate the parameter WIDTH as -16 when
// used in the test module to set the value of MSB. A number of warnings and
// errors follow, starting with:
//
// %Warning-LITENDIAN: t/t_param_module.v:42: Little bit endian vector: MSB
// < LSB of bit range: -17:0
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2013 by Jie Xu.
// SPDX-License-Identifier: CC0-1.0

// bug606

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

  localparam logic[4:0] WID = 16;
  //localparam WID = 16;        // No problem if defined like this
  wire [15:0] b33;

  test #(WID) i_test_33(.clk (clk),
                        .b   (b33));

endmodule


module test (/*AUTOARG*/
   //Inputs
   clk,
   // Outputs
   b
   );
   parameter  WIDTH = 10;
   localparam MSB   = WIDTH - 1;

   input               clk;
   output wire [MSB:0] b;

   wire [MSB:0]        a;
   assign b = {~a[MSB-1:0], clk};

   initial begin
      if ($bits(WIDTH)!=5) $stop;  // Comes from the parent!
      if ($bits(MSB)!=32) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
