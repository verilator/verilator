// DESCRIPTION: Verilator: Test pullup/pulldown with partial bus assigns
//
// This tests the case where:
// - A bus has some bits driven by pullup/pulldown through hierarchical modules
// - Other bits are driven by regular assigns (partial SEL)
// - The enable tracking must correctly handle the SEL assigns
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`default_nettype none

module pullup_mod (
    output HI
);
  pullup pullup0 (HI);
endmodule

module pulldown_mod (
    output LO
);
  pulldown pulldown0 (LO);
endmodule

module top (
    input wire [3:0] in_value,
    output wire [7:0] out_value
);
  // Lower 4 bits driven by input (partial SEL assign)
  assign out_value[3:0] = in_value;

  // Upper 4 bits: alternating pullup/pulldown through hierarchical modules
  // out_value[4] = 1 (pullup)
  // out_value[5] = 0 (pulldown)
  // out_value[6] = 1 (pullup)
  // out_value[7] = 0 (pulldown)
  pullup_mod p0 (.HI(out_value[4]));
  pulldown_mod p1 (.LO(out_value[5]));
  pullup_mod p2 (.HI(out_value[6]));
  pulldown_mod p3 (.LO(out_value[7]));
endmodule

module t;
  reg [3:0] in_value;
  wire [7:0] out_value;

  top dut (
      .in_value(in_value),
      .out_value(out_value)
  );

  logic pull_enable;
  logic [6:0] pull_data;
  bit pull_done = 0;

  // A per-bit pull must preserve the tri1 default in both packed range directions.
  tri1 [7:1] packed_default_pullup_desc;
  // verilator lint_off ASCRANGE
  tri1 [1:7] packed_default_pullup_asc;
  // verilator lint_on ASCRANGE
  pullup (packed_default_pullup_desc[3]);
  pullup (packed_default_pullup_asc[3]);
  assign packed_default_pullup_desc = pull_enable ? pull_data : 7'bz;
  assign packed_default_pullup_asc = pull_enable ? pull_data : 7'bz;

  // Likewise, preserve the tri0 default with a per-bit pulldown.
  tri0 [7:1] packed_default_pulldown_desc;
  // verilator lint_off ASCRANGE
  tri0 [1:7] packed_default_pulldown_asc;
  // verilator lint_on ASCRANGE
  pulldown (packed_default_pulldown_desc[3]);
  pulldown (packed_default_pulldown_asc[3]);
  assign packed_default_pulldown_desc = pull_enable ? pull_data : 7'bz;
  assign packed_default_pulldown_asc = pull_enable ? pull_data : 7'bz;

  initial begin
    for (int cyc = 0; cyc < 16; ++cyc) begin
      pull_enable = cyc[0];
      pull_data = 7'(cyc * 19);
      #1;
      `checkh(packed_default_pullup_desc, pull_enable ? pull_data : 7'h7f);
      `checkh(packed_default_pullup_asc, pull_enable ? pull_data : 7'h7f);
      `checkh(packed_default_pulldown_desc, pull_enable ? pull_data : 7'h00);
      `checkh(packed_default_pulldown_asc, pull_enable ? pull_data : 7'h00);
    end
    pull_done = 1;
  end

  initial begin
    // Test 1: Lower bits = 0xF
    in_value = 4'hF;
    #1;
    // Expected: 0x5F = 0101_1111
    // Bits [3:0] = F (from input)
    // Bit 4 = 1 (pullup), Bit 5 = 0 (pulldown)
    // Bit 6 = 1 (pullup), Bit 7 = 0 (pulldown)
    `checkh(out_value, 8'h5F);

    // Test 2: Lower bits = 0xA
    in_value = 4'hA;
    #1;
    // Expected: 0x5A = 0101_1010
    `checkh(out_value, 8'h5A);

    // Test 3: Lower bits = 0x0
    in_value = 4'h0;
    #1;
    // Expected: 0x50 = 0101_0000
    `checkh(out_value, 8'h50);

    wait (pull_done);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

`default_nettype wire
