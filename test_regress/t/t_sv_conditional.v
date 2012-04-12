// DESCRIPTION: Verilator: System Verilog test of case and if
//
// This code instantiates and runs a simple CPU written in System Verilog.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty.

// Contributed 2012 by M W Lund, Atmel Corporation and Jeremy Bennett, Embecosm.


module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   /*AUTOWIRE*/

   // **************************************************************************
   // Regs and Wires
   // **************************************************************************

   reg 	   rst;
   integer rst_count;


   st3_testbench st3_testbench_i (/*AUTOINST*/
				  // Inputs
				  .clk			(clk),
				  .rst			(rst));

   // **************************************************************************
   // Reset Generation
   // **************************************************************************

   initial begin
      rst       = 1'b1;
      rst_count = 0;
   end

   always @( posedge clk ) begin
      if (rst_count < 2) begin
	 rst_count++;
      end
      else begin
	 rst = 1'b0;
      end
   end

   // **************************************************************************
   // Closing message
   // **************************************************************************

   final begin
      $write("*-* All Finished *-*\n");
   end

endmodule


module st3_testbench (/*AUTOARG*/
   // Inputs
   clk, rst
   );

   input  clk;
   input  rst;

   logic  clk;
   logic  rst;
   logic [8*16-1:0] wide_input_bus;
   logic 	    decrementA;          // 0=Up-counting, 1=down-counting
   logic 	    dual_countA;         // Advance counter by 2 steps at a time
   logic 	    cntA_en;             // Enable Counter A
   logic 	    decrementB;          // 0=Up-counting, 1=down-counting
   logic 	    dual_countB;         // Advance counter by 2 steps at a time
   logic 	    cntB_en;             // Enable counter B
   logic [47:0]     selected_out;
   integer 	    i;

  
   initial begin
      decrementA = 1'b0;
      dual_countA = 1'b0;
      cntA_en = 1'b1;
      decrementB = 1'b0;
      dual_countB = 1'b0;
      cntB_en = 1'b1;
      wide_input_bus = {8'hf5,
                         8'hef,
                         8'hd5,
                         8'hc5,
                         8'hb5,
                         8'ha5,
                         8'h95,
                         8'h85,
                         8'ha7,
                         8'ha6,
                         8'ha5,
                         8'ha4,
                         8'ha3,
                         8'ha2,
                         8'ha1,
                         8'ha0};
      i = 0;
   end


   simple_test_3
     simple_test_3_i
       (// Outputs
	.selected_out                    (selected_out[47:0]),
	// Inputs
	.wide_input_bus                  (wide_input_bus[8*16-1:0]),
	.rst                             (rst),
	.clk                             (clk),
	.decrementA                      (decrementA),
	.dual_countA                     (dual_countA),
	.cntA_en                         (cntA_en),
	.decrementB                      (decrementB),
	.dual_countB                     (dual_countB),
	.cntB_en                         (cntB_en));
  

   // Logic to print outputs and then finish.
   always @(posedge clk) begin
      if (i < 50) begin
`ifdef TEST_VERBOSE
	 $display("%x", simple_test_3_i.cntA_reg ,"%x",
		  simple_test_3_i.cntB_reg ," ", "%x", selected_out);
`endif
	 i <= i + 1;
      end
      else begin
	 $finish();
      end
   end // always @ (posedge clk)

endmodule


// Module testing:
// - Unique case
// - Priority case
// - Unique if
// - ++, --, =- and =+ operands.

module simple_test_3
  (input logic [8*16-1:0] wide_input_bus,
   input logic 	       rst,
   input logic 	       clk,
   // Counter A
   input logic 	       decrementA,  // 0=Up-counting, 1=down-counting
   input logic 	       dual_countA, // Advance counter by 2 steps at a time
   input logic 	       cntA_en,     // Enable Counter A
   // Counter B
   input logic 	       decrementB,  // 0=Up-counting, 1=down-counting
   input logic 	       dual_countB, // Advance counter by 2 steps at a time
   input logic 	       cntB_en,     // Enable counter B

   // Outputs
   output logic [47:0] selected_out);
   
   // Declarations
   logic [3:0] 	       cntA_reg;       // Registered version of cntA
   logic [3:0] 	       cntB_reg;       // Registered version of cntA


   counterA
     counterA_inst
       (/*AUTOINST*/
	// Outputs
	.cntA_reg			(cntA_reg[3:0]),
	// Inputs
	.decrementA			(decrementA),
	.dual_countA			(dual_countA),
	.cntA_en			(cntA_en),
	.clk				(clk),
	.rst				(rst));
   
   counterB
     counterB_inst
       (/*AUTOINST*/
	// Outputs
	.cntB_reg			(cntB_reg[3:0]),
	// Inputs
	.decrementB			(decrementB),
	.dual_countB			(dual_countB),
	.cntB_en			(cntB_en),
	.clk				(clk),
	.rst				(rst));
   
   simple_test_3a
     sta
       (.wide_input_bus        (wide_input_bus),
	.selector              (cntA_reg),
	.selected_out          (selected_out[7:0]));
   
   simple_test_3b
     stb
       (.wide_input_bus        (wide_input_bus),
	.selector              (cntA_reg),
	.selected_out          (selected_out[15:8]));
   
   simple_test_3c
     stc
       (.wide_input_bus        (wide_input_bus),
	.selector              (cntB_reg),
	.selected_out          (selected_out[23:16]));
   
   simple_test_3d
     std
       (.wide_input_bus        (wide_input_bus),
	.selector              (cntB_reg),
	.selected_out          (selected_out[31:24]));
   
   simple_test_3e
     ste
       (.wide_input_bus        (wide_input_bus),
	.selector              (cntB_reg),
	.selected_out          (selected_out[39:32]));
   
   simple_test_3f
     stf
       (.wide_input_bus        (wide_input_bus),
	.selector              (cntB_reg),
	.selected_out          (selected_out[47:40]));

  
endmodule // simple_test_3


module counterA 
  (output logic [3:0]          cntA_reg, // Registered version of cntA
   input logic decrementA,               // 0=Up-counting, 1=down-counting
   input logic dual_countA,              // Advance counter by 2 steps at a time
   input logic cntA_en,                  // Enable Counter A
   input logic clk,                      // Clock
   input logic rst);                     // Synchronous reset
     
            
                   
   logic [3:0] cntA;                     // combinational count variable.

   // Counter A
   // Sequential part of counter CntA
   always_ff @(posedge clk)
     begin
	cntA_reg <= cntA;
     end

   // Combinational part of counter
   // Had to be split up to test C-style update, as there are no
   // non-blocking version like -<=
   always_comb
     if (rst)
       cntA = 0;
     else  begin
        cntA = cntA_reg;              // Necessary to avoid latch
        if (cntA_en) begin
           if (decrementA)
             if (dual_countA)
               //cntA = cntA - 2; 
               cntA -= 2;
             else
               //cntA = cntA - 1; 
               cntA--;
           else
             if (dual_countA)
               //cntA = cntA + 2;
               cntA += 2;
             else
               //cntA = cntA + 1; 
               cntA++;
        end // if (cntA_en)
     end
endmodule                             // counterA


module counterB
  (output logic [3:0]          cntB_reg, // Registered version of cntA
   input logic decrementB,               // 0=Up-counting, 1=down-counting
   input logic dual_countB,              // Advance counter by 2 steps at a time
   input logic cntB_en,                  // Enable counter B
   input logic clk,                      // Clock
   input logic rst);                     // Synchronous reset

   // Counter B - tried to write sequential only, but ended up without
   // SystemVerilog.  
  
   always_ff @(posedge clk) begin
      if (rst)
        cntB_reg <= 0;
      else
        if (cntB_en) begin
           if (decrementB)
             if (dual_countB)
               cntB_reg <= cntB_reg - 2;
             else
               cntB_reg <= cntB_reg - 1;
           // Attempts to write in SystemVerilog:
           else
             if (dual_countB)
               cntB_reg <= cntB_reg + 2;
             else
               cntB_reg <= cntB_reg + 1;
           // Attempts to write in SystemVerilog:
        end
   end // always_ff @
endmodule
  

// A multiplexor in terms of look-up
module simple_test_3a
  (input logic [8*16-1:0] wide_input_bus,
   input logic [3:0]  selector,
   output logic [7:0] selected_out);


   always_comb
     selected_out = {wide_input_bus[selector*8+7],
                     wide_input_bus[selector*8+6],
                     wide_input_bus[selector*8+5],
                     wide_input_bus[selector*8+4],
                     wide_input_bus[selector*8+3],
                     wide_input_bus[selector*8+2],
                     wide_input_bus[selector*8+1],
                     wide_input_bus[selector*8]};
   
endmodule // simple_test_3a


// A multiplexer in terms of standard case      
module simple_test_3b
  (input logic [8*16-1:0] wide_input_bus,
   input logic [3:0]  selector,
   output logic [7:0] selected_out);


   always_comb begin
      case (selector)
        4'h0: selected_out = wide_input_bus[  7:  0];
        4'h1: selected_out = wide_input_bus[ 15:  8];
        4'h2: selected_out = wide_input_bus[ 23: 16];
        4'h3: selected_out = wide_input_bus[ 31: 24];
        4'h4: selected_out = wide_input_bus[ 39: 32];
        4'h5: selected_out = wide_input_bus[ 47: 40];
        4'h6: selected_out = wide_input_bus[ 55: 48];
        4'h7: selected_out = wide_input_bus[ 63: 56];
        4'h8: selected_out = wide_input_bus[ 71: 64];
        4'h9: selected_out = wide_input_bus[ 79: 72];
        4'ha: selected_out = wide_input_bus[ 87: 80];
        4'hb: selected_out = wide_input_bus[ 95: 88];
        4'hc: selected_out = wide_input_bus[103: 96];
        4'hd: selected_out = wide_input_bus[111:104];
        4'he: selected_out = wide_input_bus[119:112];
        4'hf: selected_out = wide_input_bus[127:120];
      endcase // case (selector)
      
   end

endmodule // simple_test_3b


// A multiplexer in terms of unique case
module simple_test_3c
  (input logic [8*16-1:0] wide_input_bus,
   input logic [3:0]  selector,
   output logic [7:0] selected_out);


   always_comb begin
      unique case (selector) 
        4'h0: selected_out = wide_input_bus[  7:  0];
        4'h1: selected_out = wide_input_bus[ 15:  8];
        4'h2: selected_out = wide_input_bus[ 23: 16];
        4'h3: selected_out = wide_input_bus[ 31: 24];
        4'h4: selected_out = wide_input_bus[ 39: 32];
        4'h5: selected_out = wide_input_bus[ 47: 40];
        4'h6: selected_out = wide_input_bus[ 55: 48];
        4'h7: selected_out = wide_input_bus[ 63: 56];
        4'h8: selected_out = wide_input_bus[ 71: 64];
        4'h9: selected_out = wide_input_bus[ 79: 72];
        4'ha: selected_out = wide_input_bus[ 87: 80];
        4'hb: selected_out = wide_input_bus[ 95: 88];
        4'hc: selected_out = wide_input_bus[103: 96];
        4'hd: selected_out = wide_input_bus[111:104];
        4'he: selected_out = wide_input_bus[119:112];
        4'hf: selected_out = wide_input_bus[127:120];
      endcase // case (selector)
      
   end

endmodule // simple_test_3c


// A multiplexer in terms of unique if
module simple_test_3d
  (input logic [8*16-1:0] wide_input_bus,
   input logic [3:0]  selector,
   output logic [7:0] selected_out);


   always_comb begin
      unique if (selector == 4'h0) selected_out = wide_input_bus[  7:  0];
      else if (selector == 4'h1) selected_out = wide_input_bus[ 15:  8];
      else if (selector == 4'h2) selected_out = wide_input_bus[ 23: 16];
      else if (selector == 4'h3) selected_out = wide_input_bus[ 31: 24];
      else if (selector == 4'h4) selected_out = wide_input_bus[ 39: 32];
      else if (selector == 4'h5) selected_out = wide_input_bus[ 47: 40];
      else if (selector == 4'h6) selected_out = wide_input_bus[ 55: 48];
      else if (selector == 4'h7) selected_out = wide_input_bus[ 63: 56];
      else if (selector == 4'h8) selected_out = wide_input_bus[ 71: 64];
      else if (selector == 4'h9) selected_out = wide_input_bus[ 79: 72];
      else if (selector == 4'ha) selected_out = wide_input_bus[ 87: 80];
      else if (selector == 4'hb) selected_out = wide_input_bus[ 95: 88];
      else if (selector == 4'hc) selected_out = wide_input_bus[103: 96];
      else if (selector == 4'hd) selected_out = wide_input_bus[111:104];
      else if (selector == 4'he) selected_out = wide_input_bus[119:112];
      else if (selector == 4'hf) selected_out = wide_input_bus[127:120];
   end
   
endmodule // simple_test_3d


// Test of priority case
// Note: This does NOT try to implement the same function as above.
module simple_test_3e
  (input logic [8*16-1:0] wide_input_bus,
   input logic [3:0]  selector,
   output logic [7:0] selected_out);


   always_comb begin
      priority case (1'b1)
        selector[0]: selected_out = wide_input_bus[  7:  0]; // Bit 0 has highets priority
        selector[2]: selected_out = wide_input_bus[ 39: 32]; // Note 2 higher priority than 1
        selector[1]: selected_out = wide_input_bus[ 23: 16]; // Note 1 lower priority than 2
        selector[3]: selected_out = wide_input_bus[ 71: 64]; // Bit 3 has lowest priority
        default:     selected_out = wide_input_bus[127:120]; // for selector = 0.
      endcase // case (selector)
      
   end

endmodule // simple_test_3e


// Test of "inside"
// Note: This does NOT try to implement the same function as above.
// Note: Support for "inside" is a separate Verilator feature request, so is
//       not used inside a this version of the test.
module simple_test_3f
  (input logic [8*16-1:0] wide_input_bus,
   input logic [3:0]  selector,
   output logic [7:0] selected_out);


   always_comb begin      
/* -----\/----- EXCLUDED -----\/-----
      if ( selector[3:0] inside { 4'b?00?, 4'b1100})      // Matching 0000, 0001, 1000, 1100, 1001
	// if ( selector[3:2] inside { 2'b?0, selector[1:0]})
        selected_out = wide_input_bus[  7:  0];
      else
 -----/\----- EXCLUDED -----/\----- */
      /* verilator lint_off CASEOVERLAP */
        priority casez (selector[3:0])
          4'b0?10: selected_out = wide_input_bus[ 15:  8]; // Matching 0010 and 0110
          4'b0??0: selected_out = wide_input_bus[ 23: 16]; // Overlap: only 0100 remains (0000 in "if" above)
          4'b0100: selected_out = wide_input_bus[ 31: 24]; // Overlap: Will never occur
          default: selected_out = wide_input_bus[127:120];   // Remaining 0011,0100,0101,0111,1010,1011,1101,1110,1111
	endcase // case (selector)
      /* verilator lint_on CASEOVERLAP */
   end

endmodule // simple_test_3f
