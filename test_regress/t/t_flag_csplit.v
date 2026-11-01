// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2005 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  parameter CNT = 5;

  wire [31:0] w[CNT:0];

  generate
    for (genvar g = 0; g < CNT; g++)
    sub sub (
        .clk(clk),
        .i(w[g]),
        .z(w[g+1])
    );
  endgenerate

  reg [31:0] w0;
  assign w[0] = w0;

  // Members which are constructed explicitly, so the ctor/dtor of 't' is split
  int assoc[string];
  int queue[$];

  always @(posedge clk) begin
    assoc[$sformatf("%0d", cyc)] = cyc;
    queue.push_back(cyc);
    if (cyc == 10) begin
      `checkd(assoc.size(), 11);
      `checkd(assoc["10"], 10);
      `checkd(queue.size(), 11);
      `checkd(queue[10], 10);
    end
  end

  // Non-inlined instances, with strings, so their ctor/dtor is split
  subNoInline subNoInline1 (
      .clk(clk),
      .cyc(cyc)
  );
  subNoInline subNoInline2 (
      .clk(clk),
      .cyc(cyc)
  );

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      // Setup
      w0 <= 32'h1234;
    end
    else if (cyc < 90) begin
    end
    else if (cyc == 99) begin
      `define EXPECTED_SUM 32'h1239
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d  sum=%x\n", $time, cyc, w[CNT]);
`endif
      if (w[CNT] !== `EXPECTED_SUM) $stop;
      $display("cyc: %0d $past(cyc): %0d", cyc, $past(cyc));
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sub (
    input clk,
    input [31:0] i,
    output [31:0] z
);
  logic [31:0] z_tmp  /* verilator public_flat_rw */;

  always @(posedge clk) z_tmp <= i + 1 + $c("0");  // $c so doesn't optimize away

  assign z = z_tmp;

  always @(posedge z_tmp == 32'b11) begin
    $display("%m z_tmp: %0d, $past(z_tmp): $0d", z_tmp, $past(z_tmp));
  end

endmodule

module subNoInline (
    input clk,
    input integer cyc
);
  /*verilator no_inline_module*/

  // string members cause ctor/dtor of this module to split
  string s_cyc;
  string s_cyc2;
  string s_cat;

  always @(posedge clk) begin
    s_cyc <= $sformatf("%0d", cyc);
    s_cyc2 <= $sformatf("%0d", cyc * 2);
    s_cat <= {s_cyc, ":", s_cyc2};
    if (cyc == 10) `checks(s_cat, "8:16");
  end

endmodule
