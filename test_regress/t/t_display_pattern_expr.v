// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  bit [6:0] value;
  struct {bit [6:0] value;} nested;
} state_t;

typedef bit [6:0] values_t[2];

class C;
  state_t state[2];
  values_t values;
endclass

module t (
    input clk
);
  C c;
  bit [6:0] cyc = 0;

  initial c = new;

  always @(posedge clk) begin
    string expected0;
    string expected1;
    cyc++;
    c.state[0].value = cyc;
    c.state[0].nested.value = cyc + 7'd1;
    c.state[1].value = cyc + 7'd2;
    c.state[1].nested.value = cyc + 7'd3;
    expected0 = $sformatf("'{value:'h%0h, nested:'{value:'h%0h}}", cyc, cyc + 7'd1);
    expected1 = $sformatf("'{value:'h%0h, nested:'{value:'h%0h}}", cyc + 7'd2, cyc + 7'd3);
    `checks($sformatf("%p", c.state), {"'{", expected0, ", ", expected1, "}"});
    `checks($sformatf("%p", c.state[0]), expected0);
    c.values = '{cyc + 7'd4, cyc + 7'd5};
    `checks($sformatf("%p", c.values), $sformatf("'{'h%0h, 'h%0h}", cyc + 7'd4, cyc + 7'd5));
    if (cyc == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
