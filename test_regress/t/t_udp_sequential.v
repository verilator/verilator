// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Mike Thyer
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

primitive d_edge_ff(q, clock, data);
  output q;
  reg q;
  input clock, data;
initial q = 1'b1;
  table
    // clock data q q+
    // obtain output on rising edge of clock
    F 0 : ? : 0;
    (10) 1 : ? : 1;
    R 0 : ? : 1;
    (0?) 1 : ? : 0;
  endtable
endprimitive

module t (
    input clk
);
  reg d, q;
  d_edge_ff g (
      q,
      clk,
      d
  );

  // The UDP updates q like a flop, so each check sees q from the previous edge
  int cycle = 0;
  initial d = 0;
  always @(posedge clk or negedge clk) begin
    cycle <= cycle + 1;
    if (cycle == 0) begin
      d <= 1;
    end
    else if (cycle == 1) begin
      d <= 0;
      `checkd(q, 1);
    end
    else if (cycle == 2) begin
      `checkd(q, 1);
    end
    else if (cycle == 3) begin
      `checkd(q, 1);
    end
    else if (cycle == 4) begin
      d <= 1;
      `checkd(q, 0);
    end
    else if (cycle == 5) begin
      `checkd(q, 1);
    end
    else if (cycle == 6) begin
      `checkd(q, 1);
    end
    else if (cycle == 7) begin
      `checkd(q, 0);
    end
    else if (cycle == 8) begin
      `checkd(q, 1);
    end
    else if (cycle >= 9) begin
      `checkd(q, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
