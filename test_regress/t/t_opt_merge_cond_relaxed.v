// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (got), (exp)); `stop; end while(0)

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  initial begin
    #300;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  int dpiWr = 0;
  function automatic void setDpi(int value);
    dpiWr = value;
  endfunction
  export "DPI-C" function setDpi;
  import "DPI-C" context function void setViaDpi(int value); // calls setDpi(value)

  int dpiRd = 0;
  function automatic int getDpi();
    return dpiRd;
  endfunction
  export "DPI-C" function getDpi;
  import "DPI-C" context function int getViaDpi(); // calls getDpi()

  int tmp;
  int cnt = 0;

  int pub /* verilator public_flat_rd */ = 0;

  always @(posedge clk) begin

    //---------------------------
    // Mergeable

    // Side effect but no implicit state access.
    if (cyc[1]) $display("cyc[1] is 1 once");
    ++cnt;
    if (cyc[1]) $display("cyc[1] is 1 twice");

    // Side effect but no implicit state access.
    if (cyc > 100000) $error("cyc > 100000 once");
    ++cnt;
    if (cyc > 100000) $error("cyc > 100000 once");

    // DPI call, but no public state involved.
    dpiWr = 13;
    if (cyc[1:0] == 2'd2) setViaDpi(cyc + 16);
    ++cnt;
    if (cyc[1:0] == 2'd2) setViaDpi(cyc + 32);
    `check(dpiWr, cyc % 4 == 2 ? cyc + 32 : 13);

    // DPI call, but no public state involved.
    dpiRd = 24;
    tmp = 10;
    if (cyc[1:0] == 2'd1) begin
      tmp = getViaDpi();
      tmp += 10;
    end
    ++cnt;
    if (cyc[1:0] == 2'd1) begin
      tmp = getViaDpi();
      tmp += 20;
    end
    `check(tmp, cyc % 4 == 1 ? 44 : 10);

    //---------------------------
    // NOT Mergeable

    // DPI call, possible implicit state chagne.
    tmp = dpiWr;
    if (dpiWr[1:0] == 2'd2) setViaDpi(dpiWr & ~32'b11);
    if (dpiWr[1:0] == 2'd2) setViaDpi(dpiWr + 10); // Won't execute
    `check(dpiWr, cyc % 4 == 2 ? (tmp & ~32'b11) : 13);

    // DPI call, possible implicit state acces.
    dpiWr = 14;
    if (cyc[1:0] == 2'd3) setViaDpi(cyc + 32);
    ++pub;
    if (cyc[1:0] == 2'd3) setViaDpi(cyc + 64);
    `check(dpiWr, cyc % 4 == 3 ? cyc + 64 : 14);

    // DPI call, possible implicit state change.
    dpiWr = 11;
    tmp = cyc + $c(0); // Prevent repalcing with 'cyc'
    if (tmp % 3 == 0) begin
        setViaDpi(3);
        tmp = dpiWr + 2;
    end
    if (tmp % 3 == 0) setViaDpi(4); // Won't execute
    `check(dpiWr, cyc % 3 == 0 ? 3 : 11);
    dpiWr = 3;

    // DPI call, possible implicit state change.
    tmp = cyc + $c(0); // Prevent repalcing with 'cyc'
    if (tmp % 2 == 0) begin
        setViaDpi(6);
        if (cyc[2]) tmp = dpiWr + 1;
    end
    if (tmp % 2 == 0) setViaDpi(4); // Sometime executes
    `check(tmp, cyc % 2 == 0 ? (cyc[2] ? 7 : cyc) : cyc);
    `check(dpiWr, cyc % 2 == 0 ? (cyc[2] ? 6 : 4) : 3);

    // DPI call, possible implicit state read.
    dpiRd = 2;
    if (cyc[1:0] == 2'd1) begin
      dpiRd = 100;
    end
    tmp = getViaDpi();
    if (cyc[1:0] == 2'd1) begin
      dpiRd = 3;
    end
    `check(tmp, cyc % 4 == 1 ? 100 : 2);
    `check(dpiRd, cyc % 4 == 1 ? 3 : 2);

    //---------------------------
    // Dispaly so not eliminated
    $display("cnt=%3d pub=%3d", cnt, pub);
  end

endmodule
