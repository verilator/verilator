// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNOPTPUBLIC

//bug505

module t;

  parameter TOP_PARAM  /*verilator public*/ = 20;
  localparam real REAL_PARAM /*verilator public*/ = 1.25;
  localparam logic [95:0] WIDE_PARAM /*verilator public*/ = 96'h12345678_9abcdef0_12345678;
  localparam int ARRAY_PARAM[2] /*verilator public*/ = '{3, 5};

  a #(1) a1 ();
  b #(2) b2 ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module a;
  parameter ONE  /*verilator public*/ = 22;
  initial if (ONE != 1) $stop;
  // Wide multi-dimensional packed, not a C++ literal type
  localparam logic [1:0][63:0] WIDE  /*verilator public*/ = {
    64'hfedc_ba98_7654_3210, 64'h0123_4567_89ab_cdef
  };
  initial if (WIDE[0] != 64'h0123_4567_89ab_cdef) $stop;
  initial if (WIDE[1] != 64'hfedc_ba98_7654_3210) $stop;
`ifdef VERILATOR
  initial if ($c32("this->ONE") != 1) $stop;
`endif
endmodule

module b #(
    parameter TWO  /*verilator public*/ = 22
);
  initial if (TWO != 2) $stop;
`ifdef VERILATOR
  initial if ($c32("this->TWO") != 2) $stop;
`endif
endmodule

//bug804
package p;
  localparam INPACK  /*verilator public*/ = 6;
endpackage
