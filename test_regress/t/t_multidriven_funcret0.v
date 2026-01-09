// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// MULTIDRIVEN false positive - package function return var
//
// Minimal reproducer for: package function with "return expr" used in always_comb expression.
// The function return variable must not be treated as a side-effect "writeSummary" target.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package p;
  function automatic int num_bytes(input int size);
    return 1 << size;
  endfunction
endpackage

module t;
  typedef struct packed {
    logic [31:0] addr;
    logic [2:0] size;
  } meta_t;

  meta_t rd_meta_q;
  meta_t rd_meta;

  always_comb begin
    rd_meta = rd_meta_q;
    rd_meta.addr = rd_meta_q.addr + p::num_bytes(int'(rd_meta_q.size));
  end

  initial begin
    rd_meta_q.addr = 32'h100;
    rd_meta_q.size = 3'd2;  // num_bytes = 4
    #1;
    `checkd(rd_meta.addr, 32'h104);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
