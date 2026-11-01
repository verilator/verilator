// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2020 Geza Lore
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  initial begin
    // Localparams force $sformatf through the compiler's decimal conversion during
    // elaboration. The checks compare every digit, including zero-filled limbs.
    // 2^1030 + 1 exceeds 1024 bits and has a partially used top 32-bit word.
    // Binary construction keeps this check independent of decimal literal parsing.
    localparam string WIDE_DECIMAL = $sformatf("%0d", (1031'b1 << 1030) | 1031'b1);
    // The hex values are 10^18 - 1, 10^18, and 10^18 + 1, around BASE^2 for
    // base-10^9 conversion. At 10^18, a single input word produces a carry
    // requiring two new decimal limbs. Width 65 selects the wide formatting path.
    // The signed values are the minima at 7, 33, and 65 bits, checking negation
    // and sign handling on both sides of the native 64-bit formatting path.
    localparam string BOUNDARY_DECIMALS = $sformatf(
        "%0d/%0d/%0d/%0d/%0d/%0d", 65'hde0b6b3a763ffff, 65'hde0b6b3a7640000,
        65'hde0b6b3a7640001, 7'sh40, 33'sh100000000, 65'sh10000000000000000);
    `checks(WIDE_DECIMAL, {
      "1150523606311882180946755322104975829515505266523076206549952519409489125155206164049334",
      "2548634082305351687288311769174890162545204122663839542235560926343960177145179191391057",
      "6833420544797500236449973089334403692056416436699176244143304390746129431784544326838135",
      "23087356623740062701843509462805095950344781825"
    });
    `checks(BOUNDARY_DECIMALS, {
      "999999999999999999/1000000000000000000/1000000000000000001/",
      "-64/-4294967296/-18446744073709551616"
    });
  end

  int cycle;
  bit [1023:0] x;

  initial x = '1;

  always @(posedge clk) begin
    if (cycle == 0) begin
      // Format very wide constant number (which has more bits than can
      // be counted in exponent of a double precision float), with %d.
      $display(
          "%d",
          1024'hffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
    end
    else begin
      // Same, but for a variable with value only known at run-time
      $display("%d", x);
    end

    cycle <= cycle + 1;
    x <= x >> 1;

    if (cycle == 2) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
