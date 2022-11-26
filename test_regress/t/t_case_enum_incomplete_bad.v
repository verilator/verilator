// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
  logic reset=1'b1;
  logic in=1'b0;
  integer cyc = 0;
  
  
   
    
   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d in=%b reset=%b state=S%x\n", $time, cyc, in, reset, test.state);
`endif
      cyc <= cyc + 1;
      if (cyc == 2) begin
         reset <= 1'b0;// assert reset
         in    <= 1'b1;// 
      end else if (cyc == 4) begin
         reset <= 1'b1;// deassert reset
      end else if (cyc == 5) begin
         in    <= 1'b1;// 
      end else if (cyc == 10) begin
         if (test.state == 2'b00 || test.state == 2'b01 || test.state == 2'b10 ) begin
             $write("*-* All Finished *-*\n");
         end else begin
             $write("*-* wrong state *-*\n");
             $write("[%0t] cyc==%0d in=%b reset=%b state=S%x\n", $time, cyc, in, reset, test.state);
             $stop;
         end
         $finish;
      end
   end
  
 
  


   Test test(/*AUTOINST*/
             .clk(clk),
             .reset(reset),
             .in   (in   )
             );
endmodule

module Test(/*AUTOARG*/
   input logic clk,
   input logic reset,
   input logic in
   );

enum logic [1:0] {S0,S1,S2,S3} state, next;

always_ff @(posedge clk or negedge reset) begin
      if ( reset==1'b0 ) begin
          state <= S0;
       end else begin
         state <= next;
       end
end

  always_comb begin: set_next_state
    next = state; 
     unique case ( state )
      S0: if (in==1'b1) 
           next = S1;
          else
           next = S0;
      S1: if (in==1'b0) 
            next = S2;
          else if (in==1'b1)
            next = S3;
      S2: if (in==1'b1) 
            next = S1;
          else if (in==1'b0)
            next = S2;
    endcase
  
  end: set_next_state

endmodule

    

