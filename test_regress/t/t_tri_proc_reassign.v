// DESCRIPTION: Verilator: Tristate assignments within one procedural block
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface tri_proc_if;
  logic [6:0] whole_result;
  logic [3:0] partial_result;
endinterface

module t (
    input clk
);

  int cyc = 0;
  logic [5:0] select = '0;
  logic [6:0] result;
  logic enable_a = 1'b0;
  logic enable_b = 1'b0;
  logic enable_lo = 1'b0;
  logic enable_hi = 1'b0;
  logic clear_lo = 1'b0;
  logic [1:0] index = 2'd0;
  logic [3:0] partial_result;
  logic [3:0] concat_result;
  logic [3:0] indexed_result;
  tri_proc_if proc_if ();
  // verilator lint_off MULTIDRIVEN
  logic [6:0] multi_result;
  // verilator lint_on MULTIDRIVEN

  always_comb begin
    result = 'z;
    case (select)
      6'h2a: result = 7'h55;
      6'h2b: result = 7'h00;
      6'h2c: result = 7'bzz_00010;
      default: ;
    endcase
  end

  always_comb begin
    multi_result = 'z;
    if (enable_a) multi_result = 7'h01;
  end

  always_comb begin
    multi_result = 'z;
    if (enable_b) multi_result = 7'h04;
  end

  always_comb begin
    partial_result = 'z;
    if (enable_lo) partial_result[1:0] = 2'b01;
    if (enable_hi) partial_result[3:2] = 2'b10;
    if (clear_lo) partial_result[0] = 1'b0;
  end

  always_comb begin
    concat_result = 'z;
    if (enable_lo) {concat_result[3], concat_result[0]} = 2'b10;
  end

  always_comb begin
    indexed_result = 'z;
    if (enable_lo) indexed_result[index] = 1'b1;
  end

  always_comb begin
    proc_if.whole_result = 'z;
    if (enable_a) proc_if.whole_result = 7'h21;
  end

  always_comb begin
    proc_if.partial_result = 'z;
    if (enable_lo) proc_if.partial_result[2:1] = 2'b10;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      select <= 6'h2a;
      enable_a <= 1'b1;
      enable_lo <= 1'b1;
      enable_hi <= 1'b1;
    end
    else if (cyc == 1) begin
      `checkh(result, 7'h55);
      `checkh(multi_result, 7'h01);
      `checkh(partial_result, 4'b1001);
      `checkh(concat_result, 4'b1zz0);
      `checkh(indexed_result, 4'bzzz1);
      `checkh(proc_if.whole_result, 7'h21);
      `checkh(proc_if.partial_result, 4'bz10z);
      select <= 6'h2b;
      enable_a <= 1'b0;
      enable_b <= 1'b1;
      clear_lo <= 1'b1;
      index <= 2'd2;
    end
    else if (cyc == 2) begin
      `checkh(result, 7'h00);
      `checkh(multi_result, 7'h04);
      `checkh(partial_result, 4'b1000);
      `checkh(concat_result, 4'b1zz0);
      `checkh(indexed_result, 4'bz1zz);
      `checkh(proc_if.whole_result, 7'hzz);
      `checkh(proc_if.partial_result, 4'bz10z);
      select <= 6'h2c;
      enable_b <= 1'b0;
      enable_hi <= 1'b0;
      clear_lo <= 1'b0;
    end
    else if (cyc == 3) begin
      `checkh(result, 7'bzz_00010);
      `checkh(multi_result, 7'hzz);
      `checkh(partial_result, 4'bzz01);
      `checkh(concat_result, 4'b1zz0);
      `checkh(indexed_result, 4'bz1zz);
      `checkh(proc_if.whole_result, 7'hzz);
      `checkh(proc_if.partial_result, 4'bz10z);
      select <= 6'h00;
      enable_lo <= 1'b0;
    end
    else if (cyc == 4) begin
      `checkh(result, 7'hzz);
      `checkh(partial_result, 4'bzzzz);
      `checkh(concat_result, 4'bzzzz);
      `checkh(indexed_result, 4'bzzzz);
      `checkh(proc_if.whole_result, 7'hzz);
      `checkh(proc_if.partial_result, 4'bzzzz);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
