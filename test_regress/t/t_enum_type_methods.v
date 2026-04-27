// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2014 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  typedef enum [3:0] {
                E01 = 1,
                E03 = 3,
                E04 = 4
                } my_t;

  integer cyc = 0;
  my_t e;

  int arrayfits[e.num];  // Check can use as constant

  typedef struct {
    my_t m_a;
    my_t m_b;
  } mystr_t;
  mystr_t mystr;

  string s;

  // Check constification
  initial begin
    e = E03;
    `checkh(e.first, E01);
    `checkh(e.last, E04);
    `checkh(e.last(), E04);
    `checkh(e.next, E04);
    `checkh(e.next(), E04);
    `checkh(e.next(1), E04);
    `checkh(e.next(1).next(1), E01);
    `checkh(e.next(2), E01);
    `checkh(e.next(1).next(1).next(1), E03);
    `checkh(e.next(1).next(2), E03);
    `checkh(e.next(THREE), E03);
    `checkh(e.prev, E01);
    `checkh(e.prev(1), E01);
    `checkh(e.prev(1).prev(1), E04);
    `checkh(e.prev(2), E04);
    `checkh(e.num, 3);
    `checks(e.name, "E03");
    //
    s = "";
    for (my_t e = e.first; e != e.last; e = e.next) begin
      s = {s, e.name};
    end
    e = e.last;
    s = {s, e.name};
    `checks(s, "E01E03E04");
    //
    e = E04;
    s = $sformatf("%p", e);
    `checks(s, "E04");
    s = $sformatf("%p", E03);
    `checks(s, "E03");
    s = $sformatf("%s", E03);  // Non-standard but majority
    `checks(s, "E03");
    //
    mystr.m_a = E03;
    mystr.m_b = E04;
    s = $sformatf("%p", mystr);
    `checks(s, "'{m_a:E03, m_b:E04}");
  end

  localparam THREE = 3;

  // Check runtime
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      // Setup
      e <= E01;
    end
    else if (cyc == 1) begin
      `checks(e.name, "E01");
      `checkh(e.next, E03);
      `checkh(e.next(1), E03);
      `checkh(e.next(2), E04);
      `checkh(e.prev, E04);
      `checkh(e.prev(1), E04);
      `checkh(e.prev(2), E03);
      e <= E03;
    end
    else if (cyc == 2) begin
      `checks(e.name, "E03");
      `checkh(e.next, E04);
      `checkh(e.next(1), E04);
      `checkh(e.next(2), E01);
      `checkh(e.prev, E01);
      `checkh(e.prev(1), E01);
      `checkh(e.prev(2), E04);
      e <= E04;
    end
    else if (cyc == 3) begin
      `checks(e.name, "E04");
      `checkh(e.next, E01);
      `checkh(e.next(1), E01);
      `checkh(e.next(2), E03);
      `checkh(e.prev, E03);
      `checkh(e.prev(1), E03);
      `checkh(e.prev(2), E01);
      e <= E01;
      //
      s = $sformatf("%p", e);
      `checks(s, "E04");
    end
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
