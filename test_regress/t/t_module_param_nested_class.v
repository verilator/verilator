// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Each specialization of a parameterized module or class must use its own
// specialization of a parameterized class nested in it.

module sub #(
    int P = 1
);
  class Cls #(
      int Q
  );
    function int get_q();
      return Q;
    endfunction
  endclass

  Cls #(P) obj;

  function int get_q();
    if (obj == null) obj = new;
    return obj.get_q();
  endfunction
endmodule

class Outer #(
    type T = int
);
  class Inner #(
      type U
  );
    function int get_w();
      return $bits(U);
    endfunction
  endclass

  Inner #(T) obj;

  function int get_w();
    if (obj == null) obj = new;
    return obj.get_w();
  endfunction
endclass

// The recursive instance passes P through unchanged, so the specializations
// below rec5 differ from those below rec0 only in P.
module rec #(
    int P = 0,
    int D = 0
) (
    output int o
);
  class Cls #(
      int Q
  );
    static function int get_q();
      return Q;
    endfunction
  endclass

  if (D < 2) begin : g_rec
    rec #(
        .P(P),
        .D(D + 1)
    ) sub (
        .o(o)
    );
  end
  else begin : g_leaf
    assign o = Cls#(P)::get_q();
  end
endmodule

module t (
    input clk
);
  sub #(2) sub2 ();
  sub #(3) sub3 ();
  sub sub1 ();
  initial begin
    `checkd(sub2.get_q(), 2);
    `checkd(sub3.get_q(), 3);
    `checkd(sub1.get_q(), 1);
  end

  initial begin
    automatic Outer #(logic [6:0]) outer7 = new;
    automatic Outer #(logic [14:0]) outer15 = new;
    automatic Outer outer32 = new;
    `checkd(outer7.get_w(), 7);
    `checkd(outer15.get_w(), 15);
    `checkd(outer32.get_w(), 32);
  end

  int rec5_o;
  int rec0_o;
  rec #(.P(5)) rec5 (.o(rec5_o));
  rec rec0 (.o(rec0_o));
  always @(posedge clk) begin
    `checkd(rec5_o, 5);
    `checkd(rec0_o, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
