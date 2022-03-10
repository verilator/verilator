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


  // real RTL code snippet:

  logic [3:0] count_d;
  logic [3:0] count_q = '0;

  logic [3:0] want_count_d;
  logic [3:0] want_count_q = '0;

  always_ff @(posedge clk) begin : flops
    count_q        <= count_d;
    want_count_q   <= want_count_d;
  end

  always @(posedge clk) begin : simple_check
    if (cyc > 0) begin
      //$display("%m: cyc=%0d, count_q (%0d), want_count_q (%0d)",
      //         cyc, count_q, want_count_q);
      if (count_q !== want_count_q) begin
        $error("%m: cyc=%0d, count_q (%0d) !== want_count_q (%0d)",
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


endmodule
