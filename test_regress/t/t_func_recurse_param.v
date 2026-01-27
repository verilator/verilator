// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  function automatic int recurse_self;
    input int i;
    int r1;
    int r2;
    // Simulator support for statics in constant functions get varying results, not testing
    static int local_static = 10;
    automatic int local_automatic;  // check each function call resets to zero
    if (i == 0) begin
      local_static = 0;
      recurse_self = 0;
    end
    else begin
      local_static = local_static + 1;
      local_automatic = local_automatic + 10;
      recurse_self = i + recurse_self(i - 1) * 2 + recurse_self(i - 1) * 3 + local_automatic;
    end
  endfunction

  localparam int F0 = recurse_self(0);
  localparam int F3 = recurse_self(3);
  localparam int F4 = recurse_self(4);

  initial begin
    `checkd(F0, 0);
    `checkd(F3, 348);
    `checkd(F4, 1754);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
