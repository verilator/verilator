// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Adrien Le Masle.
// SPDX-License-Identifier: CC0-1.0

interface test_if #(parameter int AA = 2, BB=5);

   logic [AA-1 : 0]     a;
   logic [BB-1 : 0]     b;
   logic                c;
   logic                d;

   modport slave (input  a,
                  input  b,
                  input  c,
                  input  d);

   modport master (output a,
                   output b,
                   output c,
                   output d);

endinterface : test_if

module test
  (input logic [28:0]  a,
   output logic [28:0] b);

   always_comb begin
      b = a;
   end
endmodule

module multi_driven
  (
   input logic [20-1 : 0] data_in,
   output logic [20-1 : 0] data_out,
   test_if.slave  test_if_in,
   test_if.master test_if_out
   );

   test test_inst
     (
      .a({data_in,
          test_if_in.a,
          test_if_in.b,
          test_if_in.c,
          test_if_in.d}),
      .b({data_out,
          test_if_out.a,
          test_if_out.b,
          test_if_out.c,
          test_if_out.d}));

endmodule;
