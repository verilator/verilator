// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface a_if #(
    parameter int a_param = 0
) ();
  logic [a_param-1:0] x;

  function void to_if(input logic [a_param-1:0] x_in);
    x = x_in;
  endfunction
  function logic [a_param-1:0] from_if();
    return x;
  endfunction
endinterface

module tb ();
  genvar a;

  generate
    for (a = 1; a < 3; a++) begin : gen_a
      a_if #(.a_param(a)) a_if_a ();
      initial begin
        #1;
        a_if_a.to_if(a);
      end
    end
  endgenerate

  initial begin
    #1;
    #1;
    `checkd(gen_a[1].a_if_a.from_if(), 'h1);
    `checkd(gen_a[2].a_if_a.from_if(), 'h2);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
