// DESCRIPTION: Verilator: Test alias of a strength-assigned net with a const port
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

module t;
  reg [6:0] a;
  wire [6:0] y;

  top dut (
      .a(a),
      .y(y)
  );

  initial begin
    a = 7'd0;
    repeat (10) begin
      #1;
      `checkh(y, a + 7'd1);
      a = a + 7'd23;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module top (input [6:0] a, output [6:0] y);
  mid m (
      .sig(a),
      .y(y)
  );
endmodule

module mid (input [6:0] sig, output [6:0] y);
  /* verilator lint_off MULTIDRIVEN */
  // The strength assignment intentionally overrides the hollow child's output
  wire [6:0] w;
  sub_out so (.o(w));
  sub_in si (
      .i(w),
      .y(y)
  );
  assign (supply1, supply0) w = sig;
  /* verilator lint_on MULTIDRIVEN */
endmodule

// Hollow child: output is a constant, input is never read
module sub_out (output [6:0] o);
  assign o = 7'h12;
endmodule

module sub_in (input [6:0] i, output [6:0] y);
  assign y = i + 7'd1;
endmodule
