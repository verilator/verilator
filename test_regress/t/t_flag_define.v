// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Special cases of "string parameters" :
// This table compares obtain results from big-3 simulators to Verilator
// expected behavior. Base specified integer literals are also included as
// string detection may impact results for such cases.
//
// | In the options file       | simulator 1 | simulator 2 | simulator 3 | verilator   |
// |----------------------- ---|-------------|-------------|-------------|-------------|
// | +define+C0='"AB CD"'      | AB CD       | UNSUPPORTED | AB CD       | AB CD       |
// | +define+C1=\"AB\ CD\"     | AB CD       | UNSUPPORTED | AB CD       | AB CD       |
// | +define+C2="\"AB CD\""    | AB CD       | AB CD       | UNSUPPORTED | AB CD       |
// | +define+C3="\"AB\ CD\""   | AB CD       | AB CD       | UNSUPPORTED | AB CD       |
// | +define+C4=32'h600D600D   | UNSUPPORTED | 32'h600D600D| 32'h600D600D| 32'h600D600D|
// | +define+C5=32\'h600D600D  | 32'h600D600D| UNSUPPORTED | UNSUPPORTED | 32'h600D600D|
// | +define+C6="32'h600D600D" | 32'h600D600D| 32'h600D600D| 32'h600D600D| 32'h600D600D|
// | +define+C7='AB CD'        | AB CD       | UNSUPPORTED | UNSUPPORTED | UNSUPPORTED |

`define STRINGIFY(x) `"x`"

module t;
   initial begin
`ifdef D1A
      if (`STRINGIFY(`D4B) !== "") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D2A
      if (`STRINGIFY(`D2A) !== "VALA") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D3A
      if (`STRINGIFY(`D4B) !== "") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D3B
      if (`STRINGIFY(`D4B) !== "") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D4A
      if (`STRINGIFY(`D4A) !== "VALA") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D4B
      if (`STRINGIFY(`D4B) !== "") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D5A
      if (`STRINGIFY(`D5A) !== "VALA") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef D5A
      if (`STRINGIFY(`D5B) !== "VALB") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef STRING1
      if (`STRING1 !== "New String") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef STRING2
      if (`STRING2 !== "New String") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef STRING3
      if (`STRING3 !== "New String") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef LIT1
      if (`STRINGIFY(`LIT1) !== "32'h600D600D") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef LIT2
      if (`STRINGIFY(`LIT2) !== "32'h600D600D") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

`ifdef LIT3
      if (`STRINGIFY(`LIT3) !== "32'h600D600D") $stop;
`else
      $write("%%Error: Missing define\n"); $stop;
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
