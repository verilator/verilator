// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_case_huge_sub (/*AUTOARG*/
   // Outputs
   outa, outb, outc,
   // Inputs
   index
   );

   input [7:0] index;
   output [9:0] outa;
   output [1:0] outb;
   output 	outc;

   // =============================
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [9:0]		outa;
   reg [1:0]		outb;
   reg			outc;
   // End of automatics

   // =============================
   // Created from perl
   // for $i (0..1023) { printf "\t10'h%03x: begin outa = 10'h%03x; outb = 2'b%02b; outc = 1'b%d; end\n", $i, rand(1024),rand(4),rand(2); };

   always @(/*AS*/index) begin
      case (index)
	8'h00: begin outa = 10'h152; outb = 2'b00; outc = 1'b1; end
	8'h01: begin outa = 10'h318; outb = 2'b11; outc = 1'b1; end
	8'h02: begin outa = 10'h29f; outb = 2'b11; outc = 1'b0; end
	8'h03: begin outa = 10'h392; outb = 2'b01; outc = 1'b1; end
	8'h04: begin outa = 10'h1ef; outb = 2'b00; outc = 1'b0; end
	8'h05: begin outa = 10'h06c; outb = 2'b10; outc = 1'b1; end
	8'h06: begin outa = 10'h29f; outb = 2'b11; outc = 1'b0; end
	8'h07: begin outa = 10'h29a; outb = 2'b10; outc = 1'b0; end
	8'h08: begin outa = 10'h3ce; outb = 2'b01; outc = 1'b0; end
	8'h09: begin outa = 10'h37c; outb = 2'b01; outc = 1'b0; end
	8'h0a: begin outa = 10'h058; outb = 2'b10; outc = 1'b0; end
	8'h0b: begin outa = 10'h3b2; outb = 2'b01; outc = 1'b1; end
	8'h0c: begin outa = 10'h36f; outb = 2'b11; outc = 1'b0; end
	8'h0d: begin outa = 10'h2c5; outb = 2'b11; outc = 1'b0; end
	8'h0e: begin outa = 10'h23a; outb = 2'b00; outc = 1'b0; end
	8'h0f: begin outa = 10'h222; outb = 2'b01; outc = 1'b1; end
	8'h10: begin outa = 10'h328; outb = 2'b00; outc = 1'b1; end
	8'h11: begin outa = 10'h3c3; outb = 2'b00; outc = 1'b1; end
	8'h12: begin outa = 10'h12c; outb = 2'b01; outc = 1'b0; end
	8'h13: begin outa = 10'h1d0; outb = 2'b00; outc = 1'b1; end
	8'h14: begin outa = 10'h3ff; outb = 2'b01; outc = 1'b1; end
	8'h15: begin outa = 10'h115; outb = 2'b11; outc = 1'b1; end
	8'h16: begin outa = 10'h3ba; outb = 2'b10; outc = 1'b0; end
	8'h17: begin outa = 10'h3ba; outb = 2'b00; outc = 1'b0; end
	8'h18: begin outa = 10'h10d; outb = 2'b00; outc = 1'b1; end
	8'h19: begin outa = 10'h13b; outb = 2'b01; outc = 1'b1; end
	8'h1a: begin outa = 10'h0a0; outb = 2'b10; outc = 1'b1; end
	8'h1b: begin outa = 10'h264; outb = 2'b11; outc = 1'b0; end
	8'h1c: begin outa = 10'h3a2; outb = 2'b10; outc = 1'b0; end
	8'h1d: begin outa = 10'h07c; outb = 2'b00; outc = 1'b1; end
	8'h1e: begin outa = 10'h291; outb = 2'b00; outc = 1'b0; end
	8'h1f: begin outa = 10'h1d1; outb = 2'b10; outc = 1'b0; end
	8'h20: begin outa = 10'h354; outb = 2'b11; outc = 1'b1; end
	8'h21: begin outa = 10'h0c0; outb = 2'b00; outc = 1'b1; end
	8'h22: begin outa = 10'h191; outb = 2'b00; outc = 1'b0; end
	8'h23: begin outa = 10'h379; outb = 2'b01; outc = 1'b0; end
	8'h24: begin outa = 10'h073; outb = 2'b00; outc = 1'b0; end
	8'h25: begin outa = 10'h2fd; outb = 2'b11; outc = 1'b1; end
	8'h26: begin outa = 10'h2e0; outb = 2'b11; outc = 1'b1; end
	8'h27: begin outa = 10'h337; outb = 2'b01; outc = 1'b1; end
	8'h28: begin outa = 10'h2c7; outb = 2'b11; outc = 1'b1; end
	8'h29: begin outa = 10'h19e; outb = 2'b11; outc = 1'b0; end
	8'h2a: begin outa = 10'h107; outb = 2'b10; outc = 1'b0; end
	8'h2b: begin outa = 10'h06a; outb = 2'b01; outc = 1'b1; end
	8'h2c: begin outa = 10'h1c7; outb = 2'b01; outc = 1'b1; end
	8'h2d: begin outa = 10'h107; outb = 2'b10; outc = 1'b0; end
	8'h2e: begin outa = 10'h0cf; outb = 2'b01; outc = 1'b1; end
	8'h2f: begin outa = 10'h009; outb = 2'b11; outc = 1'b1; end
	8'h30: begin outa = 10'h09d; outb = 2'b00; outc = 1'b1; end
	8'h31: begin outa = 10'h28e; outb = 2'b00; outc = 1'b0; end
	8'h32: begin outa = 10'h010; outb = 2'b01; outc = 1'b0; end
	8'h33: begin outa = 10'h1e0; outb = 2'b10; outc = 1'b0; end
	8'h34: begin outa = 10'h079; outb = 2'b01; outc = 1'b1; end
	8'h35: begin outa = 10'h13e; outb = 2'b10; outc = 1'b1; end
	8'h36: begin outa = 10'h282; outb = 2'b11; outc = 1'b0; end
	8'h37: begin outa = 10'h21c; outb = 2'b11; outc = 1'b1; end
	8'h38: begin outa = 10'h148; outb = 2'b00; outc = 1'b1; end
	8'h39: begin outa = 10'h3c0; outb = 2'b10; outc = 1'b0; end
	8'h3a: begin outa = 10'h176; outb = 2'b01; outc = 1'b1; end
	8'h3b: begin outa = 10'h3fc; outb = 2'b10; outc = 1'b1; end
	8'h3c: begin outa = 10'h295; outb = 2'b11; outc = 1'b1; end
	8'h3d: begin outa = 10'h113; outb = 2'b10; outc = 1'b1; end
	8'h3e: begin outa = 10'h354; outb = 2'b01; outc = 1'b1; end
	8'h3f: begin outa = 10'h0db; outb = 2'b11; outc = 1'b0; end
	8'h40: begin outa = 10'h238; outb = 2'b01; outc = 1'b0; end
	8'h41: begin outa = 10'h12b; outb = 2'b01; outc = 1'b1; end
	8'h42: begin outa = 10'h1dc; outb = 2'b10; outc = 1'b0; end
	8'h43: begin outa = 10'h137; outb = 2'b01; outc = 1'b1; end
	8'h44: begin outa = 10'h1e2; outb = 2'b01; outc = 1'b1; end
	8'h45: begin outa = 10'h3d5; outb = 2'b11; outc = 1'b1; end
	8'h46: begin outa = 10'h30c; outb = 2'b11; outc = 1'b0; end
	8'h47: begin outa = 10'h298; outb = 2'b11; outc = 1'b0; end
	8'h48: begin outa = 10'h080; outb = 2'b00; outc = 1'b1; end
	8'h49: begin outa = 10'h35a; outb = 2'b11; outc = 1'b1; end
	8'h4a: begin outa = 10'h01b; outb = 2'b00; outc = 1'b0; end
	8'h4b: begin outa = 10'h0a3; outb = 2'b11; outc = 1'b0; end
	8'h4c: begin outa = 10'h0b3; outb = 2'b11; outc = 1'b1; end
	8'h4d: begin outa = 10'h17a; outb = 2'b00; outc = 1'b0; end
	8'h4e: begin outa = 10'h3ae; outb = 2'b11; outc = 1'b0; end
	8'h4f: begin outa = 10'h078; outb = 2'b11; outc = 1'b0; end
	8'h50: begin outa = 10'h322; outb = 2'b00; outc = 1'b1; end
	8'h51: begin outa = 10'h213; outb = 2'b11; outc = 1'b0; end
	8'h52: begin outa = 10'h11a; outb = 2'b11; outc = 1'b0; end
	8'h53: begin outa = 10'h1a7; outb = 2'b00; outc = 1'b0; end
	8'h54: begin outa = 10'h35a; outb = 2'b00; outc = 1'b1; end
	8'h55: begin outa = 10'h233; outb = 2'b00; outc = 1'b0; end
	8'h56: begin outa = 10'h01d; outb = 2'b01; outc = 1'b1; end
	8'h57: begin outa = 10'h2d5; outb = 2'b00; outc = 1'b0; end
	8'h58: begin outa = 10'h1a0; outb = 2'b00; outc = 1'b1; end
	8'h59: begin outa = 10'h3d0; outb = 2'b00; outc = 1'b1; end
	8'h5a: begin outa = 10'h181; outb = 2'b01; outc = 1'b1; end
	8'h5b: begin outa = 10'h219; outb = 2'b01; outc = 1'b1; end
	8'h5c: begin outa = 10'h26a; outb = 2'b01; outc = 1'b1; end
	8'h5d: begin outa = 10'h050; outb = 2'b10; outc = 1'b0; end
	8'h5e: begin outa = 10'h189; outb = 2'b10; outc = 1'b0; end
	8'h5f: begin outa = 10'h1eb; outb = 2'b01; outc = 1'b1; end
	8'h60: begin outa = 10'h224; outb = 2'b00; outc = 1'b1; end
	8'h61: begin outa = 10'h2fe; outb = 2'b00; outc = 1'b0; end
	8'h62: begin outa = 10'h0ae; outb = 2'b00; outc = 1'b1; end
	8'h63: begin outa = 10'h1cd; outb = 2'b00; outc = 1'b0; end
	8'h64: begin outa = 10'h273; outb = 2'b10; outc = 1'b1; end
	8'h65: begin outa = 10'h268; outb = 2'b10; outc = 1'b0; end
	8'h66: begin outa = 10'h111; outb = 2'b01; outc = 1'b0; end
	8'h67: begin outa = 10'h1f9; outb = 2'b00; outc = 1'b0; end
	8'h68: begin outa = 10'h232; outb = 2'b00; outc = 1'b1; end
	8'h69: begin outa = 10'h255; outb = 2'b11; outc = 1'b0; end
	8'h6a: begin outa = 10'h34c; outb = 2'b01; outc = 1'b1; end
	8'h6b: begin outa = 10'h049; outb = 2'b01; outc = 1'b1; end
	8'h6c: begin outa = 10'h197; outb = 2'b11; outc = 1'b0; end
	8'h6d: begin outa = 10'h0fe; outb = 2'b11; outc = 1'b0; end
	8'h6e: begin outa = 10'h253; outb = 2'b01; outc = 1'b1; end
	8'h6f: begin outa = 10'h2de; outb = 2'b11; outc = 1'b0; end
	8'h70: begin outa = 10'h13b; outb = 2'b10; outc = 1'b1; end
	8'h71: begin outa = 10'h040; outb = 2'b10; outc = 1'b0; end
	8'h72: begin outa = 10'h0b4; outb = 2'b00; outc = 1'b1; end
	8'h73: begin outa = 10'h233; outb = 2'b11; outc = 1'b1; end
	8'h74: begin outa = 10'h198; outb = 2'b00; outc = 1'b1; end
	8'h75: begin outa = 10'h018; outb = 2'b00; outc = 1'b1; end
	8'h76: begin outa = 10'h2f7; outb = 2'b00; outc = 1'b1; end
	8'h77: begin outa = 10'h134; outb = 2'b11; outc = 1'b0; end
	8'h78: begin outa = 10'h1ca; outb = 2'b10; outc = 1'b0; end
	8'h79: begin outa = 10'h286; outb = 2'b10; outc = 1'b1; end
	8'h7a: begin outa = 10'h0e6; outb = 2'b11; outc = 1'b1; end
	8'h7b: begin outa = 10'h064; outb = 2'b10; outc = 1'b1; end
	8'h7c: begin outa = 10'h257; outb = 2'b00; outc = 1'b1; end
	8'h7d: begin outa = 10'h31a; outb = 2'b10; outc = 1'b1; end
	8'h7e: begin outa = 10'h247; outb = 2'b01; outc = 1'b0; end
	8'h7f: begin outa = 10'h299; outb = 2'b00; outc = 1'b0; end
	8'h80: begin outa = 10'h02c; outb = 2'b00; outc = 1'b0; end
	8'h81: begin outa = 10'h2bb; outb = 2'b11; outc = 1'b0; end
	8'h82: begin outa = 10'h180; outb = 2'b10; outc = 1'b0; end
	8'h83: begin outa = 10'h245; outb = 2'b01; outc = 1'b1; end
	8'h84: begin outa = 10'h0da; outb = 2'b10; outc = 1'b0; end
	8'h85: begin outa = 10'h367; outb = 2'b10; outc = 1'b0; end
	8'h86: begin outa = 10'h304; outb = 2'b01; outc = 1'b0; end
	8'h87: begin outa = 10'h38b; outb = 2'b11; outc = 1'b0; end
	8'h88: begin outa = 10'h09f; outb = 2'b01; outc = 1'b0; end
	8'h89: begin outa = 10'h1f0; outb = 2'b10; outc = 1'b1; end
	8'h8a: begin outa = 10'h281; outb = 2'b10; outc = 1'b1; end
	8'h8b: begin outa = 10'h019; outb = 2'b00; outc = 1'b0; end
	8'h8c: begin outa = 10'h1f2; outb = 2'b10; outc = 1'b0; end
	8'h8d: begin outa = 10'h0b1; outb = 2'b01; outc = 1'b1; end
	8'h8e: begin outa = 10'h058; outb = 2'b01; outc = 1'b1; end
	8'h8f: begin outa = 10'h39b; outb = 2'b00; outc = 1'b1; end
	8'h90: begin outa = 10'h2ec; outb = 2'b10; outc = 1'b1; end
	8'h91: begin outa = 10'h250; outb = 2'b00; outc = 1'b1; end
	8'h92: begin outa = 10'h3f4; outb = 2'b10; outc = 1'b1; end
	8'h93: begin outa = 10'h057; outb = 2'b10; outc = 1'b1; end
	8'h94: begin outa = 10'h18f; outb = 2'b01; outc = 1'b1; end
	8'h95: begin outa = 10'h105; outb = 2'b01; outc = 1'b1; end
	8'h96: begin outa = 10'h1ae; outb = 2'b00; outc = 1'b1; end
	8'h97: begin outa = 10'h04e; outb = 2'b10; outc = 1'b0; end
	8'h98: begin outa = 10'h240; outb = 2'b11; outc = 1'b0; end
	8'h99: begin outa = 10'h3e4; outb = 2'b01; outc = 1'b0; end
	8'h9a: begin outa = 10'h3c6; outb = 2'b01; outc = 1'b0; end
	8'h9b: begin outa = 10'h109; outb = 2'b00; outc = 1'b1; end
	8'h9c: begin outa = 10'h073; outb = 2'b10; outc = 1'b1; end
	8'h9d: begin outa = 10'h19f; outb = 2'b01; outc = 1'b0; end
	8'h9e: begin outa = 10'h3b8; outb = 2'b01; outc = 1'b0; end
	8'h9f: begin outa = 10'h00e; outb = 2'b00; outc = 1'b1; end
	8'ha0: begin outa = 10'h1b3; outb = 2'b11; outc = 1'b1; end
	8'ha1: begin outa = 10'h2bd; outb = 2'b11; outc = 1'b0; end
	8'ha2: begin outa = 10'h324; outb = 2'b00; outc = 1'b1; end
	8'ha3: begin outa = 10'h343; outb = 2'b10; outc = 1'b0; end
	8'ha4: begin outa = 10'h1c9; outb = 2'b01; outc = 1'b0; end
	8'ha5: begin outa = 10'h185; outb = 2'b00; outc = 1'b1; end
	8'ha6: begin outa = 10'h37a; outb = 2'b00; outc = 1'b1; end
	8'ha7: begin outa = 10'h0e0; outb = 2'b01; outc = 1'b1; end
	8'ha8: begin outa = 10'h0a3; outb = 2'b10; outc = 1'b0; end
	8'ha9: begin outa = 10'h019; outb = 2'b11; outc = 1'b0; end
	8'haa: begin outa = 10'h099; outb = 2'b00; outc = 1'b1; end
	8'hab: begin outa = 10'h376; outb = 2'b01; outc = 1'b1; end
	8'hac: begin outa = 10'h077; outb = 2'b00; outc = 1'b1; end
	8'had: begin outa = 10'h2b1; outb = 2'b11; outc = 1'b1; end
	8'hae: begin outa = 10'h27f; outb = 2'b00; outc = 1'b0; end
	8'haf: begin outa = 10'h265; outb = 2'b11; outc = 1'b0; end
	8'hb0: begin outa = 10'h156; outb = 2'b10; outc = 1'b1; end
	8'hb1: begin outa = 10'h1ce; outb = 2'b00; outc = 1'b0; end
	8'hb2: begin outa = 10'h008; outb = 2'b01; outc = 1'b0; end
	8'hb3: begin outa = 10'h12e; outb = 2'b11; outc = 1'b1; end
	8'hb4: begin outa = 10'h199; outb = 2'b11; outc = 1'b0; end
	8'hb5: begin outa = 10'h330; outb = 2'b10; outc = 1'b0; end
	8'hb6: begin outa = 10'h1ab; outb = 2'b01; outc = 1'b1; end
	8'hb7: begin outa = 10'h3bd; outb = 2'b00; outc = 1'b0; end
	8'hb8: begin outa = 10'h0ca; outb = 2'b10; outc = 1'b0; end
	8'hb9: begin outa = 10'h367; outb = 2'b00; outc = 1'b0; end
	8'hba: begin outa = 10'h334; outb = 2'b00; outc = 1'b0; end
	8'hbb: begin outa = 10'h040; outb = 2'b00; outc = 1'b1; end
	8'hbc: begin outa = 10'h1a7; outb = 2'b10; outc = 1'b1; end
	8'hbd: begin outa = 10'h036; outb = 2'b11; outc = 1'b1; end
	8'hbe: begin outa = 10'h223; outb = 2'b11; outc = 1'b1; end
	8'hbf: begin outa = 10'h075; outb = 2'b01; outc = 1'b0; end
	8'hc0: begin outa = 10'h3c4; outb = 2'b00; outc = 1'b1; end
	8'hc1: begin outa = 10'h2cc; outb = 2'b01; outc = 1'b0; end
	8'hc2: begin outa = 10'h123; outb = 2'b01; outc = 1'b0; end
	8'hc3: begin outa = 10'h3fd; outb = 2'b01; outc = 1'b1; end
	8'hc4: begin outa = 10'h11e; outb = 2'b00; outc = 1'b0; end
	8'hc5: begin outa = 10'h27c; outb = 2'b11; outc = 1'b1; end
	8'hc6: begin outa = 10'h1e2; outb = 2'b11; outc = 1'b0; end
	8'hc7: begin outa = 10'h377; outb = 2'b11; outc = 1'b0; end
	8'hc8: begin outa = 10'h33a; outb = 2'b11; outc = 1'b0; end
	8'hc9: begin outa = 10'h32d; outb = 2'b11; outc = 1'b1; end
	8'hca: begin outa = 10'h014; outb = 2'b11; outc = 1'b0; end
	8'hcb: begin outa = 10'h332; outb = 2'b10; outc = 1'b0; end
	8'hcc: begin outa = 10'h359; outb = 2'b00; outc = 1'b0; end
	8'hcd: begin outa = 10'h0a4; outb = 2'b10; outc = 1'b1; end
	8'hce: begin outa = 10'h348; outb = 2'b00; outc = 1'b1; end
	8'hcf: begin outa = 10'h04b; outb = 2'b11; outc = 1'b1; end
	8'hd0: begin outa = 10'h147; outb = 2'b10; outc = 1'b1; end
	8'hd1: begin outa = 10'h026; outb = 2'b00; outc = 1'b1; end
	8'hd2: begin outa = 10'h103; outb = 2'b00; outc = 1'b0; end
	8'hd3: begin outa = 10'h106; outb = 2'b00; outc = 1'b1; end
	8'hd4: begin outa = 10'h35a; outb = 2'b00; outc = 1'b0; end
	8'hd5: begin outa = 10'h254; outb = 2'b01; outc = 1'b0; end
	8'hd6: begin outa = 10'h0cd; outb = 2'b01; outc = 1'b0; end
	8'hd7: begin outa = 10'h17c; outb = 2'b11; outc = 1'b1; end
	8'hd8: begin outa = 10'h37e; outb = 2'b10; outc = 1'b1; end
	8'hd9: begin outa = 10'h0a9; outb = 2'b11; outc = 1'b1; end
	8'hda: begin outa = 10'h0fe; outb = 2'b01; outc = 1'b0; end
	8'hdb: begin outa = 10'h3c0; outb = 2'b11; outc = 1'b1; end
	8'hdc: begin outa = 10'h1d9; outb = 2'b10; outc = 1'b1; end
	8'hdd: begin outa = 10'h10e; outb = 2'b00; outc = 1'b1; end
	8'hde: begin outa = 10'h394; outb = 2'b01; outc = 1'b0; end
	8'hdf: begin outa = 10'h316; outb = 2'b01; outc = 1'b0; end
	8'he0: begin outa = 10'h05b; outb = 2'b11; outc = 1'b0; end
	8'he1: begin outa = 10'h126; outb = 2'b01; outc = 1'b1; end
	8'he2: begin outa = 10'h369; outb = 2'b11; outc = 1'b0; end
	8'he3: begin outa = 10'h291; outb = 2'b10; outc = 1'b1; end
	8'he4: begin outa = 10'h2ca; outb = 2'b00; outc = 1'b1; end
	8'he5: begin outa = 10'h25b; outb = 2'b01; outc = 1'b1; end
	8'he6: begin outa = 10'h106; outb = 2'b00; outc = 1'b0; end
	8'he7: begin outa = 10'h172; outb = 2'b11; outc = 1'b1; end
	8'he8: begin outa = 10'h2f7; outb = 2'b00; outc = 1'b1; end
	8'he9: begin outa = 10'h2d3; outb = 2'b11; outc = 1'b1; end
	8'hea: begin outa = 10'h182; outb = 2'b00; outc = 1'b0; end
	8'heb: begin outa = 10'h327; outb = 2'b00; outc = 1'b1; end
	8'hec: begin outa = 10'h1d0; outb = 2'b10; outc = 1'b0; end
	8'hed: begin outa = 10'h204; outb = 2'b00; outc = 1'b1; end
	8'hee: begin outa = 10'h11f; outb = 2'b00; outc = 1'b1; end
	8'hef: begin outa = 10'h365; outb = 2'b11; outc = 1'b1; end
	8'hf0: begin outa = 10'h2c2; outb = 2'b01; outc = 1'b1; end
	8'hf1: begin outa = 10'h2b5; outb = 2'b10; outc = 1'b0; end
	8'hf2: begin outa = 10'h1f8; outb = 2'b10; outc = 1'b1; end
	8'hf3: begin outa = 10'h2a7; outb = 2'b01; outc = 1'b1; end
	8'hf4: begin outa = 10'h1be; outb = 2'b10; outc = 1'b1; end
	8'hf5: begin outa = 10'h25e; outb = 2'b10; outc = 1'b1; end
	8'hf6: begin outa = 10'h032; outb = 2'b10; outc = 1'b0; end
	8'hf7: begin outa = 10'h2ef; outb = 2'b00; outc = 1'b0; end
	8'hf8: begin outa = 10'h02f; outb = 2'b00; outc = 1'b1; end
	8'hf9: begin outa = 10'h201; outb = 2'b10; outc = 1'b0; end
	8'hfa: begin outa = 10'h054; outb = 2'b01; outc = 1'b1; end
	8'hfb: begin outa = 10'h013; outb = 2'b10; outc = 1'b0; end
	8'hfc: begin outa = 10'h249; outb = 2'b01; outc = 1'b0; end
	8'hfd: begin outa = 10'h09a; outb = 2'b10; outc = 1'b0; end
	8'hfe: begin outa = 10'h012; outb = 2'b00; outc = 1'b0; end
	8'hff: begin outa = 10'h114; outb = 2'b10; outc = 1'b1; end
      endcase
   end
endmodule
