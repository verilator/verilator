// DESCRIPTION: Verilator: Interface array with multiple consumer modules using FUNCREF LPARAMs
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package pkg;
  function automatic int decode_width(int value);
    return (value > 0) ? value * 2 : 0;
  endfunction
endpackage

interface ifc #(
    parameter int WIDTH = 8
);
  localparam int DEPTH = $clog2(WIDTH);
  localparam int DECODED = pkg::decode_width(DEPTH);
endinterface

module producer (
    ifc i
);
  localparam int BUF_SIZE = pkg::decode_width(i.DEPTH);
  localparam int OUT_W = i.DECODED + 1;
endmodule

module consumer (
    ifc i
);
  localparam int HALF = i.DECODED / 2;
  localparam int TAG_W = pkg::decode_width(i.DEPTH) + i.DECODED;
endmodule

module t;
  ifc #(.WIDTH(64)) bus[2] ();
  producer p (.i(bus[0]));
  consumer c (.i(bus[1]));

  initial begin
    // WIDTH=64, DEPTH=$clog2(64)=6, DECODED=decode_width(6)=12
    `checkd(p.BUF_SIZE, 12);  // decode_width(6) = 12
    `checkd(p.OUT_W, 13);  // 12 + 1 = 13
    `checkd(c.HALF, 6);  // 12 / 2 = 6
    `checkd(c.TAG_W, 24);  // decode_width(6) + 12 = 12 + 12 = 24
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
