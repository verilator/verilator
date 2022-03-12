module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

  input clk;

  int   cyc = 0;

  logic [1:0] case_sel;

  always @ (posedge clk) begin : main
    cyc <= cyc + 1;

    case_sel <= 2'($urandom);

    if (cyc > 100) begin
      $write("*-* All Finished *-*\n");
      $finish();
    end
  end


  // -------------------------
  // Simple case-stmt with ++/--

  logic [3:0] count_d;
  logic [3:0] count_q = '0;

  logic [3:0] want_count_d;
  logic [3:0] want_count_q = '0;

  always_ff @(posedge clk) begin : flops
    count_q      <= count_d;
    want_count_q <= want_count_d;
  end

  always @(posedge clk) begin : simple_check
    if (cyc > 0) begin
      if (count_q !== want_count_q) begin
        $error("%m: Checks cyc=%0d, count_q (%0d) !== want_count_q (%0d)",
               cyc, count_q, want_count_q);
        $stop; // don't finish to fail the test.
      end
    end
  end

  always_comb begin : update_golden_counts
    want_count_d = want_count_q;
    if (case_sel == 2'b10)
      want_count_d++;
    else if (case_sel == 2'b01)
      want_count_d--;
  end

  // Make sure the ++ and -- operators are handled correctly in case stmts.
  // Test for https://github.com/verilator/verilator/issues/3346
  always_comb begin : update_counts
    count_d = count_q;
    case (case_sel)
    2'b10: count_d++;
    2'b01: count_d--;
    default : ;
    endcase // case (case_sel)
  end

  // -------------------------
  // FSM with ++/--
  // A more elaborate case statement, with if-else, for loops, etc
  // to confirm that ++/-- is handled by V3LinkInc.cpp
  logic [3:0] state_d, state_q;
  initial state_q = '0;
  logic [3:0] state_counter_d, state_counter_q;
  always_ff @(posedge clk) begin
    state_q         <= state_d;
    state_counter_q <= state_counter_d;
  end


  always_comb begin : update_state
    state_d = state_q;
    state_counter_d = state_counter_q;
    case (state_q)

    // state 0, no begin/end, goes to state 1
    4'd0: state_d = 4'd1;

    // state 1, clears state_counter_d, goes to state 2
    4'd1: begin
      state_d = 4'd2;
      state_counter_d = '0;
    end

    // state 2, wait until state_counter_d increments to 4.
    4'd2: begin
      state_counter_d++;
      if (state_counter_q == 4) begin
        state_d = 4'd3;
      end
    end
    // state 3, decrements state_counter_d from 5 to 0.
    4'd3: begin
      state_counter_d--;
      if (state_counter_q == 1) begin
        state_d = 4'd4;
      end
    end

    4'd4: begin
      // add 4 with for-loop and ++.
      for (int unsigned i = 0; i < 4; i++) begin
        state_counter_d++;
      end

      if (state_counter_q == 12) begin
        state_counter_d = '0;
        state_d = 4'd5;
      end
    end

    4'd5: begin
      // add 8 with a while loop and go to state 6.
      while (state_counter_d <= 7) begin
        state_counter_d++;
      end

      if (state_counter_d == 8) begin
        state_d = 4'd15;
      end
    end
    4'd15 : begin
      // success, stay here.
      state_counter_d = 4'd7; // pick and hold some success number.
    end
    default: ;
    endcase // case (state_q)

  end // block: state

  always @(posedge clk) begin : simple_state_check
    //$display("%m: debug, cyc=%0d, state_q=%0d, state_counter_q=%0d",
    //           cyc, state_q, state_counter_q);
    if (cyc >= 90) begin
      // the above FSM should finish before 90 cycles.
      // Make sure we made it to state 4'd15.
      if (state_q !== 4'd15 ||
          state_counter_q !== 4'd7) begin
        $error("%m: EOT checks, cyc=%0d, state_q=%0d (want 15), state_counter_q=%0d (want 7)",
               cyc, state_q, state_counter_q);
        $stop; // don't finish to fail the test.
      end
    end
  end

endmodule : t
