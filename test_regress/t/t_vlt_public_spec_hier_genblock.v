// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module top (
  input  int top_port_i,
  output int top_port_o
);

  int top_tmp;

  generate
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
      int loop_local;
      sub i_sub(top_port_i, loop_local);
    end
  endgenerate

  generate
    if (1) begin : gen_if
      int if_local;
      sub i_sub(top_port_i, if_local);
    end
  endgenerate

  assign top_port_o = top_tmp;

  initial begin
    top_tmp = 0;
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module sub (
  input  int sub_port_i,
  output int sub_port_o
);
  int sub_tmp;
  assign sub_tmp = sub_port_i + 1;
  assign sub_port_o = sub_tmp;
endmodule
