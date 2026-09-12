// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef logic unsigned [31:0] uinteger;

module t;
  initial begin
    static logic unsigned [15:0] foo = 16'bz000000000000001;
    static logic signed [15:0] foo2 = 16'bz000000000000001;
    static integer bar = integer'(foo);
    if (bar !== 32'b0000000000000000z000000000000001) $stop;
    bar = uinteger'(foo2);
    if (bar !== 32'bzzzzzzzzzzzzzzzzz000000000000001) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
