// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

function automatic int ok_unused_func(real val);
  int result = $rtoi(val);
  bit huh = result[0];
  return result + huh;
endfunction

// Unused parameter
function automatic int unused_input_unused_func(int not_used);
  return 5;
endfunction

// Undriven variable
function automatic int undriven_var_unused_func(int some_val);
  int not_driven;
  return some_val + not_driven;
endfunction

function automatic int undriven_var();
  int undriven_result;
  return undriven_result;
endfunction

function automatic void undriven_output(output int undriven_out_param);
endfunction

function automatic void untouched_inout(inout int untouched_inout_param);
endfunction

function automatic void untouched_inout_unused_func(inout int untouched_inout_unused_func_param);
endfunction

function automatic void driven_inout_unused_func(inout int driven_inout_unused_func_param);
  driven_inout_unused_func_param = 7;
endfunction

function automatic void used_inout_unused_func(inout int used_inout_unused_func_param);
  $display(used_inout_unused_func_param);
endfunction

module t;
  int result;
  initial begin
    result = undriven_var();
    undriven_output(result);
    untouched_inout(result);
    $display(result);
  end
endmodule
