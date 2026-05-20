// DESCRIPTION: Verilator: Test pullup/pulldown with partial bus assigns
//
// This tests the case where:
// - A bus has some bits driven by pullup/pulldown through hierarchical modules
// - Other bits are driven by regular assigns (partial SEL)
// - The enable tracking must correctly handle the SEL assigns
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

`default_nettype none

module pullup_mod(output HI);
  pullup pullup0(HI);
endmodule

module pulldown_mod(output LO);
  pulldown pulldown0(LO);
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
  pullup_mod   p0(.HI(out_value[4]));
  pulldown_mod p1(.LO(out_value[5]));
  pullup_mod   p2(.HI(out_value[6]));
  pulldown_mod p3(.LO(out_value[7]));
endmodule

module t;
  reg [3:0] in_value;
  wire [7:0] out_value;

  top dut(.in_value(in_value), .out_value(out_value));

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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

`default_nettype wire
