// DESCRIPTION: Verilator: Verilog Test module for the atClone API
//
// This model counts from 0 to 8. It forks a child process (in C++) at 6
// and waits for the child to simulate and exit for resumption (of the parent).
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Yinan Xu.
// SPDX-License-Identifier: CC0-1.0

module top(
  input clock,
  input reset,
  input is_parent,
  output do_clone
);

reg [3:0] counter;

assign do_clone = counter == 4'h6;

always @(posedge clock) begin
  if (reset)
    counter <= 4'h0;
  else begin
    counter <= counter + 4'h1;
    $write("counter = %d\n", counter);
    $fflush();
  end

  if (counter[3]) begin
    if (is_parent) begin
      $write("*-* All Finished *-*\n");
      $fflush();
    end
    $finish(0);
  end
end


endmodule
