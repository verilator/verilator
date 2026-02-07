// DESCRIPTION: Verilator: Test interface array access with loop variables
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

interface simple_if;
  logic data;
  logic [7:0] value;

  modport source (output data, output value);
  modport sink (input data, input value);
endinterface

// Test 6: Submodule with interface array as sink modport port
module sub_sink (
  simple_if.sink ifaces [3:0],
  output logic [7:0] sum_out
);
  always_comb begin
    sum_out = 8'b0;
    for (int i = 0; i < 4; i++) begin
      sum_out = sum_out + ifaces[i].value;
    end
  end
endmodule

// Test 7: Submodule with interface array as source modport port
module sub_source (
  simple_if.source ifaces [3:0]
);
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      ifaces[i].data = 1'b1;
      ifaces[i].value = 8'(i + 100);
    end
  end
endmodule

// Test 8: Submodule with interface array without modport
module sub_generic (
  simple_if ifaces [3:0]
);
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      ifaces[i].data = 1'b0;
      ifaces[i].value = 8'(i + 50);
    end
  end
endmodule

// Test 11: Parameterized submodule with interface array size from parameter
module l1_param_sub #(
  parameter NUM_IFACES = 4
) (
  simple_if.sink l0_ifaces [NUM_IFACES-1:0],
  output logic [7:0] l0_sum
);
  always_comb begin
    l0_sum = 8'b0;
    for (int i = 0; i < NUM_IFACES; i++) begin
      l0_sum = l0_sum + l0_ifaces[i].value;
    end
  end
endmodule

module t (/*AUTOARG*/
  // Inputs
  clk
);

  input clk;

  localparam N = 4;

  simple_if ifaces [N-1:0] ();

  // Test 1: Simple for loop writing to interface array
  always_comb begin
    for (int i = 0; i < N; i++) begin
      ifaces[i].data = '0;
    end
  end

  // Test 2: For loop reading from interface array
  logic [N-1:0] read_data;
  always_comb begin
    for (int j = 0; j < N; j++) begin
      read_data[j] = ifaces[j].data;
    end
  end

  // Test 3: For loop with expression in body
  always_comb begin
    for (int k = 0; k < N-1; k++) begin
      // Use k to index, accessing different member
      ifaces[k].value = 8'(k);
    end
    ifaces[N-1].value = 8'hFF;
  end

  // Test 4: Descending loop with >= comparison
  logic [N-1:0] desc_data;
  always_comb begin
    for (int p = N-1; p >= 0; p--) begin
      desc_data[p] = ifaces[p].data;
    end
  end

  // Test 4b: Ascending loop with <= comparison
  logic [N-1:0] lte_data;
  always_comb begin
    for (int m = 0; m <= N-1; m++) begin
      lte_data[m] = ifaces[m].data;
    end
  end

  // Test 4c: Descending loop with > comparison
  simple_if gt_ifaces [N-1:0] ();
  always_comb begin
    for (int n = N; n > 0; n--) begin
      gt_ifaces[n-1].data = 1'b1;
      gt_ifaces[n-1].value = 8'(n);
    end
  end

  // Test 5: Multiple interface arrays in same loop
  simple_if other_ifaces [N-1:0] ();
  always_comb begin
    for (int q = 0; q < N; q++) begin
      other_ifaces[q].data = ifaces[q].data;
      other_ifaces[q].value = ifaces[q].value;
    end
  end

  // Test 6: Interface array as sink modport port (read from ports in loop)
  logic [7:0] sink_sum;
  sub_sink u_sub_sink (.ifaces(ifaces), .sum_out(sink_sum));

  // Test 7: Interface array as source modport port (write to ports in loop)
  simple_if source_ifaces [N-1:0] ();
  sub_source u_sub_source (.ifaces(source_ifaces));

  // Test 8: Interface array without modport (read/write in loop)
  simple_if generic_ifaces [N-1:0] ();
  sub_generic u_sub_generic (.ifaces(generic_ifaces));

  // Test 9: Ascending loop with step of 2
  simple_if step2_ifaces [7:0] ();
  always_comb begin
    for (int i = 0; i < 8; i += 2) begin
      step2_ifaces[i].data = 1'b1;
      step2_ifaces[i].value = 8'(i);
    end
    for (int i = 1; i < 8; i += 2) begin
      step2_ifaces[i].data = 1'b0;
      step2_ifaces[i].value = 8'hAA;
    end
  end

  // Test 10: Descending loop with step of -2
  simple_if step2d_ifaces [7:0] ();
  always_comb begin
    for (int i = 6; i >= 0; i -= 2) begin
      step2d_ifaces[i].data = 1'b1;
      step2d_ifaces[i].value = 8'(i);
    end
    for (int i = 7; i >= 1; i -= 2) begin
      step2d_ifaces[i].data = 1'b0;
      step2d_ifaces[i].value = 8'hBB;
    end
  end

  // Test 11: Parameterized submodule with interface array size from parameter
  // Override NUM_IFACES from default 4 to 6 to test that pre-unroll
  // uses the overridden parameter value (not the default)
  simple_if l0_param_ifaces [5:0] ();
  always_comb begin
    for (int i = 0; i < 6; i++) begin
      l0_param_ifaces[i].data = 1'b1;
      l0_param_ifaces[i].value = 8'(i * 10);
    end
  end
  logic [7:0] l0_param_sum;
  l1_param_sub #(.NUM_IFACES(6)) u_l1_param (
    .l0_ifaces(l0_param_ifaces),
    .l0_sum(l0_param_sum)
  );

  // Test 12: Complex index expression (N-1-i) - reversed assignment
  simple_if rev_ifaces [N-1:0] ();
  always_comb begin
    for (int i = 0; i < N; i++) begin
      rev_ifaces[N-1-i].data = 1'b1;
      rev_ifaces[N-1-i].value = 8'(i);
    end
  end

  // Test 13: Non-zero-based interface array range [2:5]
  simple_if nzb_ifaces [2:5] ();
  always_comb begin
    for (int i = 2; i <= 5; i++) begin
      nzb_ifaces[i].data = 1'b1;
      nzb_ifaces[i].value = 8'(i);
    end
  end

  // Verification
  int cycle;
  initial cycle = 0;

  always @(posedge clk) begin
    cycle <= cycle + 1;

    // Check that interfaces were properly accessed
    if (cycle == 1) begin
      // After initialization, data should be 0
      for (int i = 0; i < N; i++) begin
        if (ifaces[i].data !== 1'b0) begin
          $display("%%Error: ifaces[%0d].data should be 0, got %b", i, ifaces[i].data);
          $stop;
        end
      end

      // Check values
      for (int i = 0; i < N-1; i++) begin
        if (ifaces[i].value !== 8'(i)) begin
          $display("%%Error: ifaces[%0d].value should be %0d, got %0d", i, i, ifaces[i].value);
          $stop;
        end
      end
      if (ifaces[N-1].value !== 8'hFF) begin
        $display("%%Error: ifaces[%0d].value should be 0xFF, got %0d", N-1, ifaces[N-1].value);
        $stop;
      end

      // Test 4b: Check lte_data (uses <= comparison)
      for (int i = 0; i < N; i++) begin
        if (lte_data[i] !== 1'b0) begin
          $display("%%Error: lte_data[%0d] should be 0, got %b", i, lte_data[i]);
          $stop;
        end
      end

      // Test 4c: Check gt_ifaces (uses > comparison, values are 1,2,3,4)
      for (int i = 0; i < N; i++) begin
        if (gt_ifaces[i].data !== 1'b1) begin
          $display("%%Error: gt_ifaces[%0d].data should be 1, got %b", i, gt_ifaces[i].data);
          $stop;
        end
        if (gt_ifaces[i].value !== 8'(i + 1)) begin
          $display("%%Error: gt_ifaces[%0d].value should be %0d, got %0d", i, i+1, gt_ifaces[i].value);
          $stop;
        end
      end

      // Test 6: Check sink_sum (sum of ifaces[0..3].value = 0+1+2+255 = 258 = 0x02)
      if (sink_sum !== 8'h02) begin
        $display("%%Error: sink_sum should be 0x02, got 0x%02x", sink_sum);
        $stop;
      end

      // Test 7: Check source_ifaces (written by sub_source with i+100)
      for (int i = 0; i < N; i++) begin
        if (source_ifaces[i].data !== 1'b1) begin
          $display("%%Error: source_ifaces[%0d].data should be 1, got %b", i, source_ifaces[i].data);
          $stop;
        end
        if (source_ifaces[i].value !== 8'(i + 100)) begin
          $display("%%Error: source_ifaces[%0d].value should be %0d, got %0d", i, i+100, source_ifaces[i].value);
          $stop;
        end
      end

      // Test 8: Check generic_ifaces (written by sub_generic with i+50)
      for (int i = 0; i < N; i++) begin
        if (generic_ifaces[i].data !== 1'b0) begin
          $display("%%Error: generic_ifaces[%0d].data should be 0, got %b", i, generic_ifaces[i].data);
          $stop;
        end
        if (generic_ifaces[i].value !== 8'(i + 50)) begin
          $display("%%Error: generic_ifaces[%0d].value should be %0d, got %0d", i, i+50, generic_ifaces[i].value);
          $stop;
        end
      end

      // Test 9: Check step2_ifaces (even indices have i, odd have 0xAA)
      for (int i = 0; i < 8; i++) begin
        if (i % 2 == 0) begin
          if (step2_ifaces[i].data !== 1'b1) begin
            $display("%%Error: step2_ifaces[%0d].data should be 1, got %b", i, step2_ifaces[i].data);
            $stop;
          end
          if (step2_ifaces[i].value !== 8'(i)) begin
            $display("%%Error: step2_ifaces[%0d].value should be %0d, got %0d", i, i, step2_ifaces[i].value);
            $stop;
          end
        end else begin
          if (step2_ifaces[i].data !== 1'b0) begin
            $display("%%Error: step2_ifaces[%0d].data should be 0, got %b", i, step2_ifaces[i].data);
            $stop;
          end
          if (step2_ifaces[i].value !== 8'hAA) begin
            $display("%%Error: step2_ifaces[%0d].value should be 0xAA, got 0x%02x", i, step2_ifaces[i].value);
            $stop;
          end
        end
      end

      // Test 10: Check step2d_ifaces (even indices descending, odd indices 0xBB)
      for (int i = 0; i < 8; i++) begin
        if (i % 2 == 0) begin
          if (step2d_ifaces[i].data !== 1'b1) begin
            $display("%%Error: step2d_ifaces[%0d].data should be 1, got %b", i, step2d_ifaces[i].data);
            $stop;
          end
          if (step2d_ifaces[i].value !== 8'(i)) begin
            $display("%%Error: step2d_ifaces[%0d].value should be %0d, got %0d", i, i, step2d_ifaces[i].value);
            $stop;
          end
        end else begin
          if (step2d_ifaces[i].data !== 1'b0) begin
            $display("%%Error: step2d_ifaces[%0d].data should be 0, got %b", i, step2d_ifaces[i].data);
            $stop;
          end
          if (step2d_ifaces[i].value !== 8'hBB) begin
            $display("%%Error: step2d_ifaces[%0d].value should be 0xBB, got 0x%02x", i, step2d_ifaces[i].value);
            $stop;
          end
        end
      end

      // Test 11: Check l0_param_sum (0*10 + 1*10 + 2*10 + 3*10 + 4*10 + 5*10 = 150)
      if (l0_param_sum !== 8'd150) begin
        $display("%%Error: l0_param_sum should be 150, got %0d", l0_param_sum);
        $stop;
      end

      // Test 12: Check rev_ifaces (reversed: rev_ifaces[N-1-i].value = i)
      // So rev_ifaces[3].value=0, rev_ifaces[2].value=1, rev_ifaces[1].value=2, rev_ifaces[0].value=3
      for (int i = 0; i < N; i++) begin
        if (rev_ifaces[i].data !== 1'b1) begin
          $display("%%Error: rev_ifaces[%0d].data should be 1, got %b", i, rev_ifaces[i].data);
          $stop;
        end
        if (rev_ifaces[i].value !== 8'(N - 1 - i)) begin
          $display("%%Error: rev_ifaces[%0d].value should be %0d, got %0d", i, N-1-i, rev_ifaces[i].value);
          $stop;
        end
      end

      // Test 13: Check nzb_ifaces (non-zero-based [2:5], nzb_ifaces[i].value = i)
      for (int i = 2; i <= 5; i++) begin
        if (nzb_ifaces[i].data !== 1'b1) begin
          $display("%%Error: nzb_ifaces[%0d].data should be 1, got %b", i, nzb_ifaces[i].data);
          $stop;
        end
        if (nzb_ifaces[i].value !== 8'(i)) begin
          $display("%%Error: nzb_ifaces[%0d].value should be %0d, got %0d", i, i, nzb_ifaces[i].value);
          $stop;
        end
      end
    end

    if (cycle == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
