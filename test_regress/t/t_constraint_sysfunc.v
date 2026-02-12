// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test: System functions ($onehot, $onehot0, $countbits, $clog2) inside
// constraint blocks (IEEE 1800-2017 Section 18.5.12)

class test_onehot;
  rand bit [7:0] value;
  constraint c_hot {$onehot(value);}
endclass

class test_onehot0;
  rand bit [7:0] value;
  constraint c_hot0 {$onehot0(value);}
endclass

class test_countbits_ones;
  rand bit [7:0] value;
  constraint c_bits {$countbits(value, '1) == 3;}
endclass

class test_countbits_zeros;
  rand bit [7:0] value;
  constraint c_bits {$countbits(value, '0) == 6;}  // 6 zeros = 2 ones
endclass

class test_clog2;
  rand bit [7:0] data_width;
  rand bit [7:0] addr_bits;
  constraint c_log {addr_bits == 8'($clog2(data_width));}
  constraint c_nonzero {data_width > 0;}
endclass

module t;
  initial begin
    automatic test_onehot oh = new;
    automatic test_onehot0 oh0 = new;
    automatic test_countbits_ones cb1 = new;
    automatic test_countbits_zeros cb0 = new;
    automatic test_clog2 cl = new;
    automatic bit ok = 1'b1;

    // Test $onehot: exactly one bit set
    repeat (20) begin
      if (oh.randomize() == 0) $fatal(1, "$onehot randomize failed");
      if ($onehot(oh.value) !== 1'b1) begin
        $display("FAIL: $onehot value=%08b, $onehot=%0b", oh.value, $onehot(oh.value));
        ok = 1'b0;
      end
    end

    // Test $onehot0: zero or one bit set
    repeat (20) begin
      if (oh0.randomize() == 0) $fatal(1, "$onehot0 randomize failed");
      if ($onehot0(oh0.value) !== 1'b1) begin
        $display("FAIL: $onehot0 value=%08b, $onehot0=%0b", oh0.value, $onehot0(oh0.value));
        ok = 1'b0;
      end
    end

    // Test $countbits counting ones: exactly 3 ones
    repeat (20) begin
      if (cb1.randomize() == 0) $fatal(1, "$countbits('1) randomize failed");
      if ($countbits(cb1.value, '1) != 3) begin
        $display("FAIL: $countbits('1) value=%08b, count=%0d", cb1.value, $countbits(cb1.value,
                                                                                     '1));
        ok = 1'b0;
      end
    end

    // Test $countbits counting zeros: exactly 6 zeros (= 2 ones)
    repeat (20) begin
      if (cb0.randomize() == 0) $fatal(1, "$countbits('0) randomize failed");
      if ($countbits(cb0.value, '0) != 6) begin
        $display("FAIL: $countbits('0) value=%08b, zeros=%0d ones=%0d", cb0.value,
                 $countbits(cb0.value, '0), $countbits(cb0.value, '1));
        ok = 1'b0;
      end
    end

    // Test $clog2: addr_bits == $clog2(data_width)
    repeat (20) begin
      if (cl.randomize() == 0) $fatal(1, "$clog2 randomize failed");
      if (cl.addr_bits != 8'($clog2(cl.data_width))) begin
        $display("FAIL: $clog2 data_width=%0d, addr_bits=%0d, expected=%0d", cl.data_width,
                 cl.addr_bits, $clog2(cl.data_width));
        ok = 1'b0;
      end
    end

    if (ok) $display("All tests passed");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
