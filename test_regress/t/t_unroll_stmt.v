// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  int static_loop_cond;

  function logic f_loop_cond();
    return ++static_loop_cond < 8;
  endfunction

  initial begin
    // Basic loop
    for (int i = 0; i < 3; ++i) begin : loop_0
      $display("loop_0 %0d", i);
    end
    // Loop with 2 init/step
    for (int i = 0, j = 5; i < j; i += 2, j += 1) begin : loop_1
      $display("loop_1 %0d %0d", i, j);
    end
    // While loop with non-trivial init
    begin
      automatic int i = 0;
      automatic int j = 5;  // Not a variable
      while (i < j) begin : loop_2
        $display("loop_2 %0d %0d", i++, j);
      end
    end
    // Do loop with non-trivial init
    begin
      automatic int i = 5;
      automatic int j = 0;  // Not a variable
      do begin : loop_3
        $display("loop_3 %0d %0d", --i, j);
      end while (i > j);
    end
    // Do loop that executes once - replaced by V3Const, not unrolled
    do begin : loop_4
      $display("loop_4");
    end while (0);
    // Loop with inlined function as condition
    static_loop_cond = 0;
    while (f_loop_cond()) begin : loop_5
      $display("loop_5 %0d", static_loop_cond);
    end
    // Self disabling loop in via 'then' branch of 'if'
    begin
      automatic logic found = 0;
      for (int i = 0; i < 10; ++i) begin : loop_6
        if (!found) begin
          $display("loop_6 %0d", i);
          if (i == $c32("5")) begin  // Unknown condition
            $display("stopping loop_6");  // This line is important
            found = 1;
          end
        end
      end
    end
    // Done
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
