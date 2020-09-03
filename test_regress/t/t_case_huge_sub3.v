// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_case_huge_sub3 (/*AUTOARG*/
   // Outputs
   outr,
   // Inputs
   clk, index
   );

   input clk;
   input [9:0] index;
   output [3:0] outr;

   // =============================
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [3:0]		outr;
   // End of automatics

   // =============================
   // Created from perl
   //for $i (0..255) { $r=rand(4); printf "\t8'h%02x: begin outr <= outr^index[8:5]^4'h%01x; end\n", $i,
   //rand(256); };

   // Reset cheating
   initial outr = 4'b0;

   always @(posedge clk) begin
      case (index[7:0])
	8'h00: begin outr <= 4'h0; end
	8'h01: begin /*No Change*/ end
	8'h02: begin outr <= outr^index[8:5]^4'ha; end
	8'h03: begin outr <= outr^index[8:5]^4'h4; end
	8'h04: begin outr <= outr^index[8:5]^4'hd; end
	8'h05: begin outr <= outr^index[8:5]^4'h1; end
	8'h06: begin outr <= outr^index[8:5]^4'hf; end
	8'h07: begin outr <= outr^index[8:5]^4'he; end
	8'h08: begin outr <= outr^index[8:5]^4'h0; end
	8'h09: begin outr <= outr^index[8:5]^4'h4; end
	8'h0a: begin outr <= outr^index[8:5]^4'h5; end
	8'h0b: begin outr <= outr^index[8:5]^4'ha; end
	8'h0c: begin outr <= outr^index[8:5]^4'h2; end
	8'h0d: begin outr <= outr^index[8:5]^4'hf; end
	8'h0e: begin outr <= outr^index[8:5]^4'h5; end
	8'h0f: begin outr <= outr^index[8:5]^4'h0; end
	8'h10: begin outr <= outr^index[8:5]^4'h3; end
	8'h11: begin outr <= outr^index[8:5]^4'hb; end
	8'h12: begin outr <= outr^index[8:5]^4'h0; end
	8'h13: begin outr <= outr^index[8:5]^4'hf; end
	8'h14: begin outr <= outr^index[8:5]^4'h3; end
	8'h15: begin outr <= outr^index[8:5]^4'h5; end
	8'h16: begin outr <= outr^index[8:5]^4'h7; end
	8'h17: begin outr <= outr^index[8:5]^4'h2; end
	8'h18: begin outr <= outr^index[8:5]^4'h3; end
	8'h19: begin outr <= outr^index[8:5]^4'hb; end
	8'h1a: begin outr <= outr^index[8:5]^4'h5; end
	8'h1b: begin outr <= outr^index[8:5]^4'h4; end
	8'h1c: begin outr <= outr^index[8:5]^4'h2; end
	8'h1d: begin outr <= outr^index[8:5]^4'hf; end
	8'h1e: begin outr <= outr^index[8:5]^4'h0; end
	8'h1f: begin outr <= outr^index[8:5]^4'h4; end
	8'h20: begin outr <= outr^index[8:5]^4'h6; end
	8'h21: begin outr <= outr^index[8:5]^4'ha; end
	8'h22: begin outr <= outr^index[8:5]^4'h6; end
	8'h23: begin outr <= outr^index[8:5]^4'hb; end
	8'h24: begin outr <= outr^index[8:5]^4'ha; end
	8'h25: begin outr <= outr^index[8:5]^4'he; end
	8'h26: begin outr <= outr^index[8:5]^4'h7; end
	8'h27: begin outr <= outr^index[8:5]^4'ha; end
	8'h28: begin outr <= outr^index[8:5]^4'h3; end
	8'h29: begin outr <= outr^index[8:5]^4'h8; end
	8'h2a: begin outr <= outr^index[8:5]^4'h1; end
	8'h2b: begin outr <= outr^index[8:5]^4'h8; end
	8'h2c: begin outr <= outr^index[8:5]^4'h4; end
	8'h2d: begin outr <= outr^index[8:5]^4'h4; end
	8'h2e: begin outr <= outr^index[8:5]^4'he; end
	8'h2f: begin outr <= outr^index[8:5]^4'h8; end
	8'h30: begin outr <= outr^index[8:5]^4'ha; end
	8'h31: begin outr <= outr^index[8:5]^4'h7; end
	8'h32: begin outr <= outr^index[8:5]^4'h0; end
	8'h33: begin outr <= outr^index[8:5]^4'h3; end
	8'h34: begin outr <= outr^index[8:5]^4'h1; end
	8'h35: begin outr <= outr^index[8:5]^4'h3; end
	8'h36: begin outr <= outr^index[8:5]^4'h4; end
	8'h37: begin outr <= outr^index[8:5]^4'h6; end
	8'h38: begin outr <= outr^index[8:5]^4'h4; end
	8'h39: begin outr <= outr^index[8:5]^4'hb; end
	8'h3a: begin outr <= outr^index[8:5]^4'h7; end
	8'h3b: begin outr <= outr^index[8:5]^4'h1; end
	8'h3c: begin outr <= outr^index[8:5]^4'h2; end
	8'h3d: begin outr <= outr^index[8:5]^4'h0; end
	8'h3e: begin outr <= outr^index[8:5]^4'h2; end
	8'h3f: begin outr <= outr^index[8:5]^4'ha; end
	8'h40: begin outr <= outr^index[8:5]^4'h7; end
	8'h41: begin outr <= outr^index[8:5]^4'h5; end
	8'h42: begin outr <= outr^index[8:5]^4'h5; end
	8'h43: begin outr <= outr^index[8:5]^4'h4; end
	8'h44: begin outr <= outr^index[8:5]^4'h8; end
	8'h45: begin outr <= outr^index[8:5]^4'h5; end
	8'h46: begin outr <= outr^index[8:5]^4'hf; end
	8'h47: begin outr <= outr^index[8:5]^4'h6; end
	8'h48: begin outr <= outr^index[8:5]^4'h7; end
	8'h49: begin outr <= outr^index[8:5]^4'h4; end
	8'h4a: begin outr <= outr^index[8:5]^4'ha; end
	8'h4b: begin outr <= outr^index[8:5]^4'hd; end
	8'h4c: begin outr <= outr^index[8:5]^4'hb; end
	8'h4d: begin outr <= outr^index[8:5]^4'hf; end
	8'h4e: begin outr <= outr^index[8:5]^4'hd; end
	8'h4f: begin outr <= outr^index[8:5]^4'h7; end
	8'h50: begin outr <= outr^index[8:5]^4'h9; end
	8'h51: begin outr <= outr^index[8:5]^4'ha; end
	8'h52: begin outr <= outr^index[8:5]^4'hf; end
	8'h53: begin outr <= outr^index[8:5]^4'h3; end
	8'h54: begin outr <= outr^index[8:5]^4'h1; end
	8'h55: begin outr <= outr^index[8:5]^4'h0; end
	8'h56: begin outr <= outr^index[8:5]^4'h2; end
	8'h57: begin outr <= outr^index[8:5]^4'h9; end
	8'h58: begin outr <= outr^index[8:5]^4'h2; end
	8'h59: begin outr <= outr^index[8:5]^4'h4; end
	8'h5a: begin outr <= outr^index[8:5]^4'hc; end
	8'h5b: begin outr <= outr^index[8:5]^4'hd; end
	8'h5c: begin outr <= outr^index[8:5]^4'h3; end
	8'h5d: begin outr <= outr^index[8:5]^4'hb; end
	8'h5e: begin outr <= outr^index[8:5]^4'hd; end
	8'h5f: begin outr <= outr^index[8:5]^4'h7; end
	8'h60: begin outr <= outr^index[8:5]^4'h7; end
	8'h61: begin outr <= outr^index[8:5]^4'h3; end
	8'h62: begin outr <= outr^index[8:5]^4'h3; end
	8'h63: begin outr <= outr^index[8:5]^4'hb; end
	8'h64: begin outr <= outr^index[8:5]^4'h9; end
	8'h65: begin outr <= outr^index[8:5]^4'h4; end
	8'h66: begin outr <= outr^index[8:5]^4'h3; end
	8'h67: begin outr <= outr^index[8:5]^4'h6; end
	8'h68: begin outr <= outr^index[8:5]^4'h7; end
	8'h69: begin outr <= outr^index[8:5]^4'h7; end
	8'h6a: begin outr <= outr^index[8:5]^4'hf; end
	8'h6b: begin outr <= outr^index[8:5]^4'h6; end
	8'h6c: begin outr <= outr^index[8:5]^4'h8; end
	8'h6d: begin outr <= outr^index[8:5]^4'he; end
	8'h6e: begin outr <= outr^index[8:5]^4'h4; end
	8'h6f: begin outr <= outr^index[8:5]^4'h6; end
	8'h70: begin outr <= outr^index[8:5]^4'hc; end
	8'h71: begin outr <= outr^index[8:5]^4'h9; end
	8'h72: begin outr <= outr^index[8:5]^4'h5; end
	8'h73: begin outr <= outr^index[8:5]^4'ha; end
	8'h74: begin outr <= outr^index[8:5]^4'h7; end
	8'h75: begin outr <= outr^index[8:5]^4'h0; end
	8'h76: begin outr <= outr^index[8:5]^4'h1; end
	8'h77: begin outr <= outr^index[8:5]^4'he; end
	8'h78: begin outr <= outr^index[8:5]^4'ha; end
	8'h79: begin outr <= outr^index[8:5]^4'h7; end
	8'h7a: begin outr <= outr^index[8:5]^4'hf; end
	8'h7b: begin outr <= outr^index[8:5]^4'he; end
	8'h7c: begin outr <= outr^index[8:5]^4'h6; end
	8'h7d: begin outr <= outr^index[8:5]^4'hc; end
	8'h7e: begin outr <= outr^index[8:5]^4'hc; end
	8'h7f: begin outr <= outr^index[8:5]^4'h0; end
	8'h80: begin outr <= outr^index[8:5]^4'h0; end
	8'h81: begin outr <= outr^index[8:5]^4'hd; end
	8'h82: begin outr <= outr^index[8:5]^4'hb; end
	8'h83: begin outr <= outr^index[8:5]^4'hc; end
	8'h84: begin outr <= outr^index[8:5]^4'h2; end
	8'h85: begin outr <= outr^index[8:5]^4'h8; end
	8'h86: begin outr <= outr^index[8:5]^4'h3; end
	8'h87: begin outr <= outr^index[8:5]^4'ha; end
	8'h88: begin outr <= outr^index[8:5]^4'he; end
	8'h89: begin outr <= outr^index[8:5]^4'h9; end
	8'h8a: begin outr <= outr^index[8:5]^4'h1; end
	8'h8b: begin outr <= outr^index[8:5]^4'h1; end
	8'h8c: begin outr <= outr^index[8:5]^4'hc; end
	8'h8d: begin outr <= outr^index[8:5]^4'h2; end
	8'h8e: begin outr <= outr^index[8:5]^4'h2; end
	8'h8f: begin outr <= outr^index[8:5]^4'hd; end
	8'h90: begin outr <= outr^index[8:5]^4'h0; end
	8'h91: begin outr <= outr^index[8:5]^4'h6; end
	8'h92: begin outr <= outr^index[8:5]^4'h7; end
	8'h93: begin outr <= outr^index[8:5]^4'hc; end
	8'h94: begin outr <= outr^index[8:5]^4'hb; end
	8'h95: begin outr <= outr^index[8:5]^4'h3; end
	8'h96: begin outr <= outr^index[8:5]^4'h0; end
	8'h97: begin outr <= outr^index[8:5]^4'hc; end
	8'h98: begin outr <= outr^index[8:5]^4'hc; end
	8'h99: begin outr <= outr^index[8:5]^4'hb; end
	8'h9a: begin outr <= outr^index[8:5]^4'h6; end
	8'h9b: begin outr <= outr^index[8:5]^4'h5; end
	8'h9c: begin outr <= outr^index[8:5]^4'h5; end
	8'h9d: begin outr <= outr^index[8:5]^4'h4; end
	8'h9e: begin outr <= outr^index[8:5]^4'h7; end
	8'h9f: begin outr <= outr^index[8:5]^4'he; end
	8'ha0: begin outr <= outr^index[8:5]^4'hc; end
	8'ha1: begin outr <= outr^index[8:5]^4'hc; end
	8'ha2: begin outr <= outr^index[8:5]^4'h0; end
	8'ha3: begin outr <= outr^index[8:5]^4'h1; end
	8'ha4: begin outr <= outr^index[8:5]^4'hd; end
	8'ha5: begin outr <= outr^index[8:5]^4'h3; end
	8'ha6: begin outr <= outr^index[8:5]^4'hc; end
	8'ha7: begin outr <= outr^index[8:5]^4'h2; end
	8'ha8: begin outr <= outr^index[8:5]^4'h3; end
	8'ha9: begin outr <= outr^index[8:5]^4'hd; end
	8'haa: begin outr <= outr^index[8:5]^4'h5; end
	8'hab: begin outr <= outr^index[8:5]^4'hb; end
	8'hac: begin outr <= outr^index[8:5]^4'he; end
	8'had: begin outr <= outr^index[8:5]^4'h0; end
	8'hae: begin outr <= outr^index[8:5]^4'hf; end
	8'haf: begin outr <= outr^index[8:5]^4'h9; end
	8'hb0: begin outr <= outr^index[8:5]^4'hf; end
	8'hb1: begin outr <= outr^index[8:5]^4'h7; end
	8'hb2: begin outr <= outr^index[8:5]^4'h9; end
	8'hb3: begin outr <= outr^index[8:5]^4'hf; end
	8'hb4: begin outr <= outr^index[8:5]^4'he; end
	8'hb5: begin outr <= outr^index[8:5]^4'h3; end
	8'hb6: begin outr <= outr^index[8:5]^4'he; end
	8'hb7: begin outr <= outr^index[8:5]^4'h8; end
	8'hb8: begin outr <= outr^index[8:5]^4'hf; end
	8'hb9: begin outr <= outr^index[8:5]^4'hd; end
	8'hba: begin outr <= outr^index[8:5]^4'h3; end
	8'hbb: begin outr <= outr^index[8:5]^4'h5; end
	8'hbc: begin outr <= outr^index[8:5]^4'hd; end
	8'hbd: begin outr <= outr^index[8:5]^4'ha; end
	8'hbe: begin outr <= outr^index[8:5]^4'h7; end
	8'hbf: begin outr <= outr^index[8:5]^4'he; end
	8'hc0: begin outr <= outr^index[8:5]^4'h2; end
	8'hc1: begin outr <= outr^index[8:5]^4'he; end
	8'hc2: begin outr <= outr^index[8:5]^4'h9; end
	8'hc3: begin outr <= outr^index[8:5]^4'hb; end
	8'hc4: begin outr <= outr^index[8:5]^4'h0; end
	8'hc5: begin outr <= outr^index[8:5]^4'h5; end
	8'hc6: begin outr <= outr^index[8:5]^4'h9; end
	8'hc7: begin outr <= outr^index[8:5]^4'h6; end
	8'hc8: begin outr <= outr^index[8:5]^4'ha; end
	8'hc9: begin outr <= outr^index[8:5]^4'hf; end
	8'hca: begin outr <= outr^index[8:5]^4'h3; end
	8'hcb: begin outr <= outr^index[8:5]^4'hb; end
	8'hcc: begin outr <= outr^index[8:5]^4'he; end
	8'hcd: begin outr <= outr^index[8:5]^4'h2; end
	8'hce: begin outr <= outr^index[8:5]^4'h5; end
	8'hcf: begin outr <= outr^index[8:5]^4'hf; end
	8'hd0: begin outr <= outr^index[8:5]^4'h2; end
	8'hd1: begin outr <= outr^index[8:5]^4'h9; end
	8'hd2: begin outr <= outr^index[8:5]^4'hb; end
	8'hd3: begin outr <= outr^index[8:5]^4'h8; end
	8'hd4: begin outr <= outr^index[8:5]^4'h0; end
	8'hd5: begin outr <= outr^index[8:5]^4'h2; end
	8'hd6: begin outr <= outr^index[8:5]^4'hb; end
	8'hd7: begin outr <= outr^index[8:5]^4'h2; end
	8'hd8: begin outr <= outr^index[8:5]^4'ha; end
	8'hd9: begin outr <= outr^index[8:5]^4'hf; end
	8'hda: begin outr <= outr^index[8:5]^4'h8; end
	8'hdb: begin outr <= outr^index[8:5]^4'h4; end
	8'hdc: begin outr <= outr^index[8:5]^4'he; end
	8'hdd: begin outr <= outr^index[8:5]^4'h6; end
	8'hde: begin outr <= outr^index[8:5]^4'h9; end
	8'hdf: begin outr <= outr^index[8:5]^4'h9; end
	8'he0: begin outr <= outr^index[8:5]^4'h7; end
	8'he1: begin outr <= outr^index[8:5]^4'h0; end
	8'he2: begin outr <= outr^index[8:5]^4'h9; end
	8'he3: begin outr <= outr^index[8:5]^4'h3; end
	8'he4: begin outr <= outr^index[8:5]^4'h2; end
	8'he5: begin outr <= outr^index[8:5]^4'h4; end
	8'he6: begin outr <= outr^index[8:5]^4'h5; end
	8'he7: begin outr <= outr^index[8:5]^4'h5; end
	8'he8: begin outr <= outr^index[8:5]^4'hf; end
	8'he9: begin outr <= outr^index[8:5]^4'ha; end
	8'hea: begin outr <= outr^index[8:5]^4'hc; end
	8'heb: begin outr <= outr^index[8:5]^4'hd; end
	8'hec: begin outr <= outr^index[8:5]^4'h1; end
	8'hed: begin outr <= outr^index[8:5]^4'h5; end
	8'hee: begin outr <= outr^index[8:5]^4'h9; end
	8'hef: begin outr <= outr^index[8:5]^4'h0; end
	8'hf0: begin outr <= outr^index[8:5]^4'hd; end
	8'hf1: begin outr <= outr^index[8:5]^4'hf; end
	8'hf2: begin outr <= outr^index[8:5]^4'h4; end
	8'hf3: begin outr <= outr^index[8:5]^4'ha; end
	8'hf4: begin outr <= outr^index[8:5]^4'h8; end
	8'hf5: begin outr <= outr^index[8:5]^4'he; end
	8'hf6: begin outr <= outr^index[8:5]^4'he; end
	8'hf7: begin outr <= outr^index[8:5]^4'h1; end
	8'hf8: begin outr <= outr^index[8:5]^4'h6; end
	8'hf9: begin outr <= outr^index[8:5]^4'h0; end
	8'hfa: begin outr <= outr^index[8:5]^4'h5; end
	8'hfb: begin outr <= outr^index[8:5]^4'h1; end
	8'hfc: begin outr <= outr^index[8:5]^4'h8; end
	8'hfd: begin outr <= outr^index[8:5]^4'h6; end
	8'hfe: begin outr <= outr^index[8:5]^4'h1; end
	default: begin outr <= outr^index[8:5]^4'h6; end
      endcase
   end
endmodule
