// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder

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

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
