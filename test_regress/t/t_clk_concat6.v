// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

module some_module (
                    input [3:0] i_clks
                    );

   logic [ 1 : 0 ]              some_state;
   logic [1:0]                  some_other_state;
   logic                        the_clk;

   assign the_clk = i_clks[3];

   always @(posedge the_clk) begin
      case (some_state)
        2'b11:
          if (some_other_state == 0)
            some_state <= 2'b00;
        default:
          $display ("This is a display statement");
      endcase

      if (the_clk)
        some_other_state <= 0;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

`define BROKEN

module t1(
          input [3:0] i_clks,
          input       i_clk0,
          input       i_clk1
          );

   some_module
     some_module
       (
        .i_clks (i_clks)
        );
endmodule

module ident(
             input  i_ident,
             output o_ident
             );
   assign o_ident = i_ident;
endmodule

module t2(
          input [2:0] i_clks,
          input       i_clk0,
          input       i_clk1,
          input       i_clk2,
          input       i_data
          );
   logic [3:0]        the_clks;
   logic              data_q;
   logic              ident_clk1;

   always @(posedge i_clk0) begin
      data_q <= i_data;
   end

   ident
     ident
       (
        .i_ident (i_clk1),
        .o_ident (ident_clk1)
        );

   t1 t1
     (
      .i_clks ({ident_clk1, i_clk2, ident_clk1, i_clk0}),
      .i_clk0 (i_clk0),
      .i_clk1 (i_clk1)
      );
endmodule

module t(
         /*AUTOARG*/
         // Inputs
         clk /*verilator clocker*/ /*verilator public_flat*/,
         input clk0 /*verilator clocker*/,
         input clk1 /*verilator clocker*/,
         input clk2 /*verilator clocker*/,
         input data_in
         );

   input       clk;

   logic [2:0] clks;

   assign clks = {1'b0, clk1, clk0};

   t2
     t2
       (
        .i_clks (clks),
        .i_clk0 (clk0),
        .i_clk1 (clk),
        .i_clk2 (clk2),
        .i_data (data_in)
        );

endmodule
