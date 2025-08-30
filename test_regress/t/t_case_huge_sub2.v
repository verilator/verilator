// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_case_huge_sub2 (/*AUTOARG*/
  // Outputs
  outa,
  // Inputs
  index
  );

  input [9:0] index;
  output logic [9:0] outa;

  // =============================
  // Created from Python3:
  // for i in range(1024):
  //    print("      10'h%03x: begin outa = 10'h%03x; outb = 2'b%d%d; outc = 1'b%d; end"
  //        % (i, random.randint(0,1024), random.randint(0,1),
  //          random.randint(0,1), random.randint(0,1)))

  always @(/*AS*/index) begin
    case (index[7:0])
`ifdef VERILATOR  // Harder test
      8'h00: begin
        outa = $c("0");
      end  // Makes whole table non-optimizable
`else
      8'h00: outa = 10'h0;
`endif
      8'h01: outa = 10'h318;
      8'h02: outa = 10'h29f;
      8'h03: outa = 10'h392;
      8'h04: outa = 10'h1ef;
      8'h05: outa = 10'h06c;
      8'h06: outa = 10'h29f;
      8'h07: outa = 10'h29a;
      8'h08: outa = 10'h3ce;
      8'h09: outa = 10'h37c;
      8'h0a: outa = 10'h058;
      8'h0b: outa = 10'h3b2;
      8'h0c: outa = 10'h36f;
      8'h0d: outa = 10'h2c5;
      8'h0e: outa = 10'h23a;
      8'h0f: outa = 10'h222;
      8'h10: outa = 10'h328;
      8'h11: outa = 10'h3c3;
      8'h12: outa = 10'h12c;
      8'h13: outa = 10'h1d0;
      8'h14: outa = 10'h3ff;
      8'h15: outa = 10'h115;
      8'h16: outa = 10'h3ba;
      8'h17: outa = 10'h3ba;
      8'h18: outa = 10'h10d;
      8'h19: outa = 10'h13b;
      8'h1a: outa = 10'h0a0;
      8'h1b: outa = 10'h264;
      8'h1c: outa = 10'h3a2;
      8'h1d: outa = 10'h07c;
      8'h1e: outa = 10'h291;
      8'h1f: outa = 10'h1d1;
      8'h20: outa = 10'h354;
      8'h21: outa = 10'h0c0;
      8'h22: outa = 10'h191;
      8'h23: outa = 10'h379;
      8'h24: outa = 10'h073;
      8'h25: outa = 10'h2fd;
      8'h26: outa = 10'h2e0;
      8'h27: outa = 10'h337;
      8'h28: outa = 10'h2c7;
      8'h29: outa = 10'h19e;
      8'h2a: outa = 10'h107;
      8'h2b: outa = 10'h06a;
      8'h2c: outa = 10'h1c7;
      8'h2d: outa = 10'h107;
      8'h2e: outa = 10'h0cf;
      8'h2f: outa = 10'h009;
      8'h30: outa = 10'h09d;
      8'h31: outa = 10'h28e;
      8'h32: outa = 10'h010;
      8'h33: outa = 10'h1e0;
      8'h34: outa = 10'h079;
      8'h35: outa = 10'h13e;
      8'h36: outa = 10'h282;
      8'h37: outa = 10'h21c;
      8'h38: outa = 10'h148;
      8'h39: outa = 10'h3c0;
      8'h3a: outa = 10'h176;
      8'h3b: outa = 10'h3fc;
      8'h3c: outa = 10'h295;
      8'h3d: outa = 10'h113;
      8'h3e: outa = 10'h354;
      8'h3f: outa = 10'h0db;
      8'h40: outa = 10'h238;
      8'h41: outa = 10'h12b;
      8'h42: outa = 10'h1dc;
      8'h43: outa = 10'h137;
      8'h44: outa = 10'h1e2;
      8'h45: outa = 10'h3d5;
      8'h46: outa = 10'h30c;
      8'h47: outa = 10'h298;
      8'h48: outa = 10'h080;
      8'h49: outa = 10'h35a;
      8'h4a: outa = 10'h01b;
      8'h4b: outa = 10'h0a3;
      8'h4c: outa = 10'h0b3;
      8'h4d: outa = 10'h17a;
      8'h4e: outa = 10'h3ae;
      8'h4f: outa = 10'h078;
      8'h50: outa = 10'h322;
      8'h51: outa = 10'h213;
      8'h52: outa = 10'h11a;
      8'h53: outa = 10'h1a7;
      8'h54: outa = 10'h35a;
      8'h55: outa = 10'h233;
      8'h56: outa = 10'h01d;
      8'h57: outa = 10'h2d5;
      8'h58: outa = 10'h1a0;
      8'h59: outa = 10'h3d0;
      8'h5a: outa = 10'h181;
      8'h5b: outa = 10'h219;
      8'h5c: outa = 10'h26a;
      8'h5d: outa = 10'h050;
      8'h5e: outa = 10'h189;
      8'h5f: outa = 10'h1eb;
      8'h60: outa = 10'h224;
      8'h61: outa = 10'h2fe;
      8'h62: outa = 10'h0ae;
      8'h63: outa = 10'h1cd;
      8'h64: outa = 10'h273;
      8'h65: outa = 10'h268;
      8'h66: outa = 10'h111;
      8'h67: outa = 10'h1f9;
      8'h68: outa = 10'h232;
      8'h69: outa = 10'h255;
      8'h6a: outa = 10'h34c;
      8'h6b: outa = 10'h049;
      8'h6c: outa = 10'h197;
      8'h6d: outa = 10'h0fe;
      8'h6e: outa = 10'h253;
      8'h6f: outa = 10'h2de;
      8'h70: outa = 10'h13b;
      8'h71: outa = 10'h040;
      8'h72: outa = 10'h0b4;
      8'h73: outa = 10'h233;
      8'h74: outa = 10'h198;
      8'h75: outa = 10'h018;
      8'h76: outa = 10'h2f7;
      8'h77: outa = 10'h134;
      8'h78: outa = 10'h1ca;
      8'h79: outa = 10'h286;
      8'h7a: outa = 10'h0e6;
      8'h7b: outa = 10'h064;
      8'h7c: outa = 10'h257;
      8'h7d: outa = 10'h31a;
      8'h7e: outa = 10'h247;
      8'h7f: outa = 10'h299;
      8'h80: outa = 10'h02c;
      8'h81: outa = 10'h2bb;
      8'h82: outa = 10'h180;
      8'h83: outa = 10'h245;
      8'h84: outa = 10'h0da;
      8'h85: outa = 10'h367;
      8'h86: outa = 10'h304;
      8'h87: outa = 10'h38b;
      8'h88: outa = 10'h09f;
      8'h89: outa = 10'h1f0;
      8'h8a: outa = 10'h281;
      8'h8b: outa = 10'h019;
      8'h8c: outa = 10'h1f2;
      8'h8d: outa = 10'h0b1;
      8'h8e: outa = 10'h058;
      8'h8f: outa = 10'h39b;
      8'h90: outa = 10'h2ec;
      8'h91: outa = 10'h250;
      8'h92: outa = 10'h3f4;
      8'h93: outa = 10'h057;
      8'h94: outa = 10'h18f;
      8'h95: outa = 10'h105;
      8'h96: outa = 10'h1ae;
      8'h97: outa = 10'h04e;
      8'h98: outa = 10'h240;
      8'h99: outa = 10'h3e4;
      8'h9a: outa = 10'h3c6;
      8'h9b: outa = 10'h109;
      8'h9c: outa = 10'h073;
      8'h9d: outa = 10'h19f;
      8'h9e: outa = 10'h3b8;
      8'h9f: outa = 10'h00e;
      8'ha0: outa = 10'h1b3;
      8'ha1: outa = 10'h2bd;
      8'ha2: outa = 10'h324;
      8'ha3: outa = 10'h343;
      8'ha4: outa = 10'h1c9;
      8'ha5: outa = 10'h185;
      8'ha6: outa = 10'h37a;
      8'ha7: outa = 10'h0e0;
      8'ha8: outa = 10'h0a3;
      8'ha9: outa = 10'h019;
      8'haa: outa = 10'h099;
      8'hab: outa = 10'h376;
      8'hac: outa = 10'h077;
      8'had: outa = 10'h2b1;
      8'hae: outa = 10'h27f;
      8'haf: outa = 10'h265;
      8'hb0: outa = 10'h156;
      8'hb1: outa = 10'h1ce;
      8'hb2: outa = 10'h008;
      8'hb3: outa = 10'h12e;
      8'hb4: outa = 10'h199;
      8'hb5: outa = 10'h330;
      8'hb6: outa = 10'h1ab;
      8'hb7: outa = 10'h3bd;
      8'hb8: outa = 10'h0ca;
      8'hb9: outa = 10'h367;
      8'hba: outa = 10'h334;
      8'hbb: outa = 10'h040;
      8'hbc: outa = 10'h1a7;
      8'hbd: outa = 10'h036;
      8'hbe: outa = 10'h223;
      8'hbf: outa = 10'h075;
      8'hc0: outa = 10'h3c4;
      8'hc1: outa = 10'h2cc;
      8'hc2: outa = 10'h123;
      8'hc3: outa = 10'h3fd;
      8'hc4: outa = 10'h11e;
      8'hc5: outa = 10'h27c;
      8'hc6: outa = 10'h1e2;
      8'hc7: outa = 10'h377;
      8'hc8: outa = 10'h33a;
      8'hc9: outa = 10'h32d;
      8'hca: outa = 10'h014;
      8'hcb: outa = 10'h332;
      8'hcc: outa = 10'h359;
      8'hcd: outa = 10'h0a4;
      8'hce: outa = 10'h348;
      8'hcf: outa = 10'h04b;
      8'hd0: outa = 10'h147;
      8'hd1: outa = 10'h026;
      8'hd2: outa = 10'h103;
      8'hd3: outa = 10'h106;
      8'hd4: outa = 10'h35a;
      8'hd5: outa = 10'h254;
      8'hd6: outa = 10'h0cd;
      8'hd7: outa = 10'h17c;
      8'hd8: outa = 10'h37e;
      8'hd9: outa = 10'h0a9;
      8'hda: outa = 10'h0fe;
      8'hdb: outa = 10'h3c0;
      8'hdc: outa = 10'h1d9;
      8'hdd: outa = 10'h10e;
      8'hde: outa = 10'h394;
      8'hdf: outa = 10'h316;
      8'he0: outa = 10'h05b;
      8'he1: outa = 10'h126;
      8'he2: outa = 10'h369;
      8'he3: outa = 10'h291;
      8'he4: outa = 10'h2ca;
      8'he5: outa = 10'h25b;
      8'he6: outa = 10'h106;
      8'he7: outa = 10'h172;
      8'he8: outa = 10'h2f7;
      8'he9: outa = 10'h2d3;
      8'hea: outa = 10'h182;
      8'heb: outa = 10'h327;
      8'hec: outa = 10'h1d0;
      8'hed: outa = 10'h204;
      8'hee: outa = 10'h11f;
      8'hef: outa = 10'h365;
      8'hf0: outa = 10'h2c2;
      8'hf1: outa = 10'h2b5;
      8'hf2: outa = 10'h1f8;
      8'hf3: outa = 10'h2a7;
      8'hf4: outa = 10'h1be;
      8'hf5: outa = 10'h25e;
      8'hf6: outa = 10'h032;
      8'hf7: outa = 10'h2ef;
      8'hf8: outa = 10'h02f;
      8'hf9: outa = 10'h201;
      8'hfa: outa = 10'h054;
      8'hfb: outa = 10'h013;
      8'hfc: outa = 10'h249;
      8'hfd: outa = 10'h09a;
      8'hfe: outa = 10'h012;
      8'hff: outa = 10'h114;
    endcase
  end
endmodule
