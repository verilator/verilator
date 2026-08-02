// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

//bug505

module t;

  parameter WIDTH = 33;
  localparam MAX_WIDTH = 11;
  localparam NUM_OUT = num_out(WIDTH);

  wire [NUM_OUT-1:0] z;

  // verilator lint_off SIMILARNAME 
  function integer num_out;
    input integer width;
    num_out = 1;
    while ((width + num_out - 1) / num_out > MAX_WIDTH) num_out = num_out * 2;
  endfunction
  // verilator lint_on SIMILARNAME 

  initial begin
    if (NUM_OUT != 4) $stop;
    if ($bits(z) != 4) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
