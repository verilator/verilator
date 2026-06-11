// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Antmicro
// SPDX-License-Identifier: CC0-1.0

// Test case for reducing and in constraint
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rand(cl, field, gotv, expv, count) \
begin \
   automatic longint prev_result; \
   automatic int ok; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   `checkd(gotv, expv) \
   repeat(count) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      `checkd(gotv, expv) \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end
// verilog_format: on

class test_redops_bitfields #(RANDVAL_BITWIDTH=8);
  rand bit [RANDVAL_BITWIDTH-1:0] rand_val;
  rand bit redand;
  rand bit redxor;
  rand bit redor;

  constraint c {
    redand == &rand_val;
  }

  constraint d {
    redxor == ^rand_val;
  }

  constraint e {
    redor == |rand_val;
  }

  function bit calc_redand();
    bit result = 1'b1;

    foreach (rand_val[idx]) begin
      result &= rand_val[idx];
    end

    return result;
  endfunction

  function bit calc_redxor();
    bit result;

    foreach (rand_val[idx]) begin
      result ^= rand_val[idx];
    end

    return result;
  endfunction

  function bit calc_redor();
    bit result = 1'b0;

    foreach (rand_val[idx]) begin
      result |= rand_val[idx];
    end

    return result;
  endfunction

  function void verify();
    //`check_rand(this, this.rand_val, this.redand, this.calc_redand(), 20);
    `check_rand(this, this.rand_val, this.redxor, this.calc_redxor(), 20);
    //`check_rand(this, this.rand_val, this.redor, this.calc_redor(), 20);
  endfunction
endclass

module t;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(1))   redops_1bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(8))   redops_8bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(16))  redops_16bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(32))  redops_32bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(47))  redops_47bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(63))  redops_63bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(64))  redops_64bit;
  test_redops_bitfields #(.RANDVAL_BITWIDTH(128)) redops_128bit;

  initial begin
    redops_1bit = new();
    redops_1bit.verify();

    redops_8bit = new();
    redops_8bit.verify();

    redops_16bit = new();
    redops_16bit.verify();

    redops_32bit = new();
    redops_32bit.verify();

    redops_47bit = new();
    redops_47bit.verify();

    redops_63bit = new();
    redops_63bit.verify();

    redops_64bit = new();
    redops_64bit.verify();

    redops_128bit = new();
    redops_128bit.verify();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
