// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off LITENDIAN */
module some_module (
                    input wrclk
                    );

   logic [ 1 : 0 ]        some_state;
   logic [1:0]            some_other_state;

   always @(posedge wrclk) begin
      case (some_state)
        2'b11:
          if (some_other_state == 0)
            some_state <= 2'b00;
        default:
          $display ("This is a display statement");
      endcase

      if (wrclk)
        some_other_state <= 0;
   end

endmodule

`define BROKEN

module t1(
          input [-12:-9] i_clks,
          input          i_clk0,
          input          i_clk1
          );

   some_module
     some_module
       (
`ifdef BROKEN
        .wrclk (i_clks[-12])
`else
        .wrclk (i_clk1)
`endif
        );
endmodule

module t2(
          input [2:0] i_clks,
          input       i_clk0,
          input       i_clk1,
          input       i_clk2,
          input       i_data
          );
   logic [-12:-9]     the_clks;
   logic              data_q;

   assign the_clks[-12] = i_clk1;
   assign the_clks[-11] = i_clk2;
   assign the_clks[-10] = i_clk1;
   assign the_clks[-9] = i_clk0;

   always @(posedge i_clk0) begin
      data_q <= i_data;
   end

   t1 t1
     (
      .i_clks (the_clks),
      .i_clk0 (i_clk0),
      .i_clk1 (i_clk1)
      );
endmodule

module t(
         input clk0 /*verilator clocker*/,
         input clk1 /*verilator clocker*/,
         input clk2 /*verilator clocker*/,
         input data_in
         );

   logic [2:0] clks;

   assign clks = {1'b0, clk1, clk0};

   t2
     t2
       (
        .i_clks (clks),
        .i_clk0 (clk0),
        .i_clk1 (clk1),
        .i_clk2 (clk2),
        .i_data (data_in)
        );

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
