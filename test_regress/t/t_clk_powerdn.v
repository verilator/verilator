// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg   reset_l;

   // verilator lint_off GENCLK

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics

   reg   clkgate_e2r;
   reg   clkgate_e1r_l;
   always @(posedge clk or negedge reset_l) begin
      if (!reset_l) begin
         clkgate_e1r_l <= ~1'b1;
      end
      else begin
         clkgate_e1r_l <= ~clkgate_e2r;
      end
   end

   reg clkgate_e1f;
   always @(negedge clk) begin
      // Yes, it's really a =
      clkgate_e1f = ~clkgate_e1r_l | ~reset_l;
   end

   wire clkgated = clk & clkgate_e1f;

   reg [31:0] countgated;
   always @(posedge clkgated or negedge reset_l) begin
      if (!reset_l) begin
         countgated <= 32'h1000;
      end
      else begin
         countgated <= countgated + 32'd1;
      end
   end

   reg [31:0] count;
   always @(posedge clk or negedge reset_l) begin
      if (!reset_l) begin
         count <= 32'h1000;
      end
      else begin
         count <= count + 32'd1;
      end
   end

   reg [7:0] cyc; initial cyc = 0;
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] rs %x cyc %d cg1f %x cnt %x cg %x\n", $time,reset_l,cyc,clkgate_e1f,count,countgated);
`endif
      cyc <= cyc + 8'd1;
      case (cyc)
        8'd00: begin
           reset_l <= ~1'b0;
           clkgate_e2r <= 1'b1;
        end
        8'd01: begin
           reset_l <= ~1'b0;
        end
        8'd02: begin
        end
        8'd03: begin
           reset_l <= ~1'b1;    // Need a posedge
        end
        8'd04: begin
        end
        8'd05: begin
           reset_l <= ~1'b0;
        end
        8'd09: begin
           clkgate_e2r <= 1'b0;
        end
        8'd11: begin
           clkgate_e2r <= 1'b1;
        end
        8'd20: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
        default: ;
      endcase
      case (cyc)
        8'd00: ;
        8'd01: ;
        8'd02: ;
        8'd03: ;
        8'd04: if (count!=32'h00001000 || countgated!=32'h 00001000) $stop;
        8'd05: if (count!=32'h00001000 || countgated!=32'h 00001000) $stop;
        8'd06: if (count!=32'h00001000 || countgated!=32'h 00001000) $stop;
        8'd07: if (count!=32'h00001001 || countgated!=32'h 00001001) $stop;
        8'd08: if (count!=32'h00001002 || countgated!=32'h 00001002) $stop;
        8'd09: if (count!=32'h00001003 || countgated!=32'h 00001003) $stop;
        8'd10: if (count!=32'h00001004 || countgated!=32'h 00001004) $stop;
        8'd11: if (count!=32'h00001005 || countgated!=32'h 00001005) $stop;
        8'd12: if (count!=32'h00001006 || countgated!=32'h 00001005) $stop;
        8'd13: if (count!=32'h00001007 || countgated!=32'h 00001005) $stop;
        8'd14: if (count!=32'h00001008 || countgated!=32'h 00001006) $stop;
        8'd15: if (count!=32'h00001009 || countgated!=32'h 00001007) $stop;
        8'd16: if (count!=32'h0000100a || countgated!=32'h 00001008) $stop;
        8'd17: if (count!=32'h0000100b || countgated!=32'h 00001009) $stop;
        8'd18: if (count!=32'h0000100c || countgated!=32'h 0000100a) $stop;
        8'd19: if (count!=32'h0000100d || countgated!=32'h 0000100b) $stop;
        8'd20: if (count!=32'h0000100e || countgated!=32'h 0000100c) $stop;
        default: $stop;
      endcase
   end

endmodule
