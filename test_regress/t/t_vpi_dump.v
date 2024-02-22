// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


typedef struct packed {
   logic [3:0][7:0] adr;  // address
   logic [3:0][7:0] dat;  // data
   int              sel;  // select
} t_bus;

interface TestInterface();

   logic [31:0] addr;
   modport source (input addr);

endinterface


module t (  /*AUTOARG*/
    // Outputs
    x,
    // Inputs
    clk,
    a
);


   parameter int do_generate = 1;
   parameter longint long_int = 64'h123456789abcdef;


   input clk;

   input [7:0] a;
   output reg [7:0] x;

   reg onebit;
   reg [2:1] twoone;
   reg [2:1] fourthreetwoone[4:3];
   reg LONGSTART_a_very_long_name_which_will_get_hashed_a_very_long_name_which_will_get_hashed_a_very_long_name_which_will_get_hashed_a_very_long_name_which_will_get_hashed_LONGEND ;

   // verilator lint_off ASCRANGE
   reg [0:61] quads[2:3];
   // verilator lint_on ASCRANGE

   reg [31:0] count;
   reg [31:0] half_count;

   reg [7:0] text_byte;
   reg [15:0] text_half;
   reg [31:0] text_word;
   reg [63:0] text_long;
   reg [511:0] text;

   integer status;

   real real1;
   string str1;

   t_bus bus1;

   sub sub ();

   TestInterface intf_arr[2]();


   initial begin

      $write("*-* All Finished *-*\n");
      $finish();
   end


   genvar i;
   generate
      for (i = 1; i <= 2; i = i + 1) begin : arr
         arr #(.LENGTH(i)) arr ();
      end

      for (i = 1; i <= 3; i = i + 1) begin : outer_scope

         parameter int scoped_param = i * 2;

         genvar j;
         for (j = 1; j <= 3; j = j + 1) begin : inner_scope
            parameter int scoped_param_inner = scoped_param + 1;
            arr #(.LENGTH(scoped_param_inner)) arr ();

         end
      end
   endgenerate



   if (do_generate == 1) begin : cond_scope
      sub scoped_sub ();
      parameter int scoped_wire = 1;
   end else begin : cond_scope_else
      sub scoped_sub ();
      parameter int scoped_wire = 2;
   end

endmodule : t

module sub;
   reg subsig1;
   reg subsig2;
`ifdef IVERILOG
   // stop icarus optimizing signals away
   wire redundant = subsig1 | subsig2;
`endif
endmodule : sub

module arr;

   parameter LENGTH = 1;

   reg [LENGTH-1:0] sig;
   reg [LENGTH-1:0] rfr;

   reg              check;
   reg              verbose;

   initial begin
      sig = {LENGTH{1'b0}};
      rfr = {LENGTH{1'b0}};
   end

   always @(posedge check) begin
      if (verbose) $display("%m : %x %x", sig, rfr);
      if (check && sig != rfr) $stop;
      check <= 0;
   end

endmodule : arr
