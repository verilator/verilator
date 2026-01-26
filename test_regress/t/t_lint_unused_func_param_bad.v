// DESCRIPTION: Verilator: Test that unused function variables still warn in used functions
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

module t();
   foo foo_inst();
endmodule

module foo(
  input  wire [31:0] i,
  output wire [31:0] o
);
  // Used function - local variable 'unused_local' SHOULD warn (regression test)
  // This ensures we don't suppress warnings for unused variables in used functions
  // The fix only suppresses warnings when the function itself is unused
  function [31:0] foo_func;
    input [31:0] used_param;
    reg [31:0] unused_local;  // This should warn: assigned but never read
    begin
      unused_local = used_param;  // Assign but never read - should trigger UNUSEDSIGNAL
      foo_func = used_param;
    end
  endfunction
  
  // Call the function to make it used (user2() != 0)
  assign o = foo_func(i);
endmodule
