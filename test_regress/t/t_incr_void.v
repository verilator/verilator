module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

  input clk;

  int   cyc = 0;

  always @ (posedge clk) begin : main
    cyc <= cyc + 1;

    if (cyc > 100) begin
      $write("*-* All Finished *-*\n");
      $finish();
    end
  end



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
      if (count_q !== want_count_q) begin
        $error("%m: cyc=%0d, count_q (%0d) !== want_count_q (%0d)",
               cyc, count_q, want_count_q);
        $stop; // don't finish to fail the test.
      end
    end
  end

  always_comb begin : update_golden_counts
    want_count_d = want_count_q;
    want_count_d += 1'b1;
  end

  // make sure an implicit void cast on n++ works as expected.
  always_comb begin : update_counts
    count_d = count_q;
    count_d++;
  end


endmodule
