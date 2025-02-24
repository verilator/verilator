// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Andrew Ranck
// SPDX-License-Identifier: CC0-1.0

// Test for Issue#5358: Support default value on module input.

// This test is not expected to fail. There are 3 DUTs using various defaulted (and not) input values,
// with expected checks over a few cycles.


module dut_default_input0
  (
  input logic  required_input,
  input logic  i = (1'b0 && 1'b0), // 0
  output logic o
   );
  assign o = i;
endmodule


module dut_default_input1
  (
  input logic  i = 1'b1,
  input logic  required_input,
  output logic o
   );
  assign o = i;
endmodule


module dut_default_input_logic32
  #(
     parameter bit [31:0] DefaultValueI = 32'h12345678
     )
  (
  input logic [31:0]  i = DefaultValueI,
  output logic [31:0] o
   );
  assign o = i;

endmodule


module dut_default_input_wire32
  (
  input wire [31:0] i = 32'h12345678,
  output logic [31:0] o
   );
  assign o = i;
endmodule


module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

  input clk;
  int   cyc = 0;


  wire logic1 = 1'b1;

  function automatic logic logic0_from_some_function();
    return 1'b0;
  endfunction : logic0_from_some_function

  // 1800-2009, a few flavors to test:
  // 1. Port omitted from port list on instance (uses default value, NOT implicit net)
  // 2. Port included on instance and left open (uses default value)
  // 3. Port included on instance and overridden.


  // 1. DUT instances with default values and port omitted
  // instance names are u_dut*_default
  logic dut0_o_default;
  dut_default_input0 u_dut0_default
    (.required_input(1),
     /*.i(),*/
     .o(dut0_o_default));

  logic dut1_o_default;
  dut_default_input1 u_dut1_default
    (/*.i(),*/
     .o(dut1_o_default),
     .required_input(1));

  logic [31:0] dut_logic32_o_default;
  dut_default_input_logic32 u_dut_logic32_default
    (/*.i(),*/
     .o(dut_logic32_o_default));


  // 2. DUT instances with default values and port open
  // instance names are u_dut*_open
  logic        dut0_o_open;
  dut_default_input0 u_dut0_open
    (.required_input(1),
     .i(),  // open
     .o(dut0_o_open));

  logic        dut1_o_open;
  dut_default_input1 u_dut1_open
    (.i(),  // open
     .o(dut1_o_open),
     .required_input(1));

  logic [31:0] dut_logic32_o_open;
  dut_default_input_logic32 u_dut_logic32_open
    (.i(),  // open
     .o(dut_logic32_o_open));

  logic [31:0] dut_wire32_o_open;
  dut_default_input_wire32 u_dut_wire32_open
    (.i(),  // open
     .o(dut_wire32_o_open));


  // 3. DUT instances with overriden values
  // instance names are u_dut*_overriden
  // Have u_dut0_overriden get its overriden value from a signal
  logic        dut0_o_overriden;
  dut_default_input0 u_dut0_overriden
    (.required_input(1),
     .i(logic1),  // from wire
     .o(dut0_o_overriden));

  // Have u_dut1_overriden get its overriden value from a function.
  logic        dut1_o_overriden;
  dut_default_input1 u_dut1_overriden
    (.i(logic0_from_some_function()),  // from function
     .o(dut1_o_overriden),
     .required_input(1));

  logic [31:0] dut_logic32_o_overriden;
  logic [31:0] dut_logic32_want_overriden;
  dut_default_input_logic32
    #(.DefaultValueI(32'h2222_3333) // dontcare, we're overriding on input
      )
   u_dut_logic32_overriden
    (.i(32'h6789_2345 + 32'(cyc)),  // from inline logic
     .o(dut_logic32_o_overriden));
  assign dut_logic32_want_overriden = 32'h6789_2345 + 32'(cyc); // expected value i --> o


  always @(posedge clk) begin : main
    cyc <= cyc + 1;

    if (cyc > 2) begin
      // check these for a few cycles to make sure it's constant

      $display("%t %m: outputs  - defaults got {%0d %0d %0x}, want {0 1 12345678}",
               $time,
               dut0_o_default, dut1_o_default, dut_logic32_o_default);

      if (dut0_o_default != 0) $error;
      if (dut1_o_default != 1) $error;
      if (dut_logic32_o_default != 32'h1234_5678) $error;

      $display("%t %m: outputs  - open got {%0d %0d %0x}, want {0 1 12345678}",
               $time,
               dut0_o_open, dut1_o_open, dut_logic32_o_open);

      if (dut0_o_open != 0) $error;
      if (dut1_o_open != 1) $error;
      if (dut_logic32_o_open != 32'h1234_5678) $error;
      if (dut_wire32_o_open != 32'h1234_5678) $error;

      // despite the port map override. At least the parameter goes through?
      $display("%t %m: outputs  - overrides got {%0d %0d %0x} want {1 0 %0x}",
               $time,
               dut0_o_overriden, dut1_o_overriden, dut_logic32_o_overriden,
               dut_logic32_want_overriden);

      if (dut0_o_overriden != 1) $error;
      if (dut1_o_overriden != 0) $error;
      if (dut_logic32_o_overriden != dut_logic32_want_overriden) $error;


    end

    if (cyc == 10) begin
      // done checking various DUTs and finish
      $display("%t %m: cyc=%0d", $time, cyc);
      $write("*-* All Finished *-*\n");
      $finish();
    end

  end

endmodule : t
