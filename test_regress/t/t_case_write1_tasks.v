// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

module t_case_write1_tasks ();

   // verilator lint_off WIDTH
   // verilator lint_off CASEINCOMPLETE

   parameter STRLEN = 78;
   task ozonerab;
      input [6:0] rab;
      inout [STRLEN*8:1] foobar;
      // verilator no_inline_task
      begin
	 case (rab[6:0])
	   7'h00 : foobar = {foobar, " 0"};
	   7'h01 : foobar = {foobar, " 1"};
	   7'h02 : foobar = {foobar, " 2"};
	   7'h03 : foobar = {foobar, " 3"};
	   7'h04 : foobar = {foobar, " 4"};
	   7'h05 : foobar = {foobar, " 5"};
	   7'h06 : foobar = {foobar, " 6"};
	   7'h07 : foobar = {foobar, " 7"};
	   7'h08 : foobar = {foobar, " 8"};
	   7'h09 : foobar = {foobar, " 9"};
	   7'h0a : foobar = {foobar, " 10"};
	   7'h0b : foobar = {foobar, " 11"};
	   7'h0c : foobar = {foobar, " 12"};
	   7'h0d : foobar = {foobar, " 13"};
	   7'h0e : foobar = {foobar, " 14"};
	   7'h0f : foobar = {foobar, " 15"};
	   7'h10 : foobar = {foobar, " 16"};
	   7'h11 : foobar = {foobar, " 17"};
	   7'h12 : foobar = {foobar, " 18"};
	   7'h13 : foobar = {foobar, " 19"};
	   7'h14 : foobar = {foobar, " 20"};
	   7'h15 : foobar = {foobar, " 21"};
	   7'h16 : foobar = {foobar, " 22"};
	   7'h17 : foobar = {foobar, " 23"};
	   7'h18 : foobar = {foobar, " 24"};
	   7'h19 : foobar = {foobar, " 25"};
	   7'h1a : foobar = {foobar, " 26"};
	   7'h1b : foobar = {foobar, " 27"};
	   7'h1c : foobar = {foobar, " 28"};
	   7'h1d : foobar = {foobar, " 29"};
	   7'h1e : foobar = {foobar, " 30"};
	   7'h1f : foobar = {foobar, " 31"};
	   7'h20 : foobar = {foobar, " 32"};
	   7'h21 : foobar = {foobar, " 33"};
	   7'h22 : foobar = {foobar, " 34"};
	   7'h23 : foobar = {foobar, " 35"};
	   7'h24 : foobar = {foobar, " 36"};
	   7'h25 : foobar = {foobar, " 37"};
	   7'h26 : foobar = {foobar, " 38"};
	   7'h27 : foobar = {foobar, " 39"};
	   7'h28 : foobar = {foobar, " 40"};
	   7'h29 : foobar = {foobar, " 41"};
	   7'h2a : foobar = {foobar, " 42"};
	   7'h2b : foobar = {foobar, " 43"};
	   7'h2c : foobar = {foobar, " 44"};
	   7'h2d : foobar = {foobar, " 45"};
	   7'h2e : foobar = {foobar, " 46"};
	   7'h2f : foobar = {foobar, " 47"};
	   7'h30 : foobar = {foobar, " 48"};
	   7'h31 : foobar = {foobar, " 49"};
	   7'h32 : foobar = {foobar, " 50"};
	   7'h33 : foobar = {foobar, " 51"};
	   7'h34 : foobar = {foobar, " 52"};
	   7'h35 : foobar = {foobar, " 53"};
	   7'h36 : foobar = {foobar, " 54"};
	   7'h37 : foobar = {foobar, " 55"};
	   7'h38 : foobar = {foobar, " 56"};
	   7'h39 : foobar = {foobar, " 57"};
	   7'h3a : foobar = {foobar, " 58"};
	   7'h3b : foobar = {foobar, " 59"};
	   7'h3c : foobar = {foobar, " 60"};
	   7'h3d : foobar = {foobar, " 61"};
	   7'h3e : foobar = {foobar, " 62"};
	   7'h3f : foobar = {foobar, " 63"};
	   7'h40 : foobar = {foobar, " 64"};
	   7'h41 : foobar = {foobar, " 65"};
	   7'h42 : foobar = {foobar, " 66"};
	   7'h43 : foobar = {foobar, " 67"};
	   7'h44 : foobar = {foobar, " 68"};
	   7'h45 : foobar = {foobar, " 69"};
	   7'h46 : foobar = {foobar, " 70"};
	   7'h47 : foobar = {foobar, " 71"};
	   7'h48 : foobar = {foobar, " 72"};
	   7'h49 : foobar = {foobar, " 73"};
	   7'h4a : foobar = {foobar, " 74"};
	   7'h4b : foobar = {foobar, " 75"};
	   7'h4c : foobar = {foobar, " 76"};
	   7'h4d : foobar = {foobar, " 77"};
	   7'h4e : foobar = {foobar, " 78"};
	   7'h4f : foobar = {foobar, " 79"};
	   7'h50 : foobar = {foobar, " 80"};
	   7'h51 : foobar = {foobar, " 81"};
	   7'h52 : foobar = {foobar, " 82"};
	   7'h53 : foobar = {foobar, " 83"};
	   7'h54 : foobar = {foobar, " 84"};
	   7'h55 : foobar = {foobar, " 85"};
	   7'h56 : foobar = {foobar, " 86"};
	   7'h57 : foobar = {foobar, " 87"};
	   7'h58 : foobar = {foobar, " 88"};
	   7'h59 : foobar = {foobar, " 89"};
	   7'h5a : foobar = {foobar, " 90"};
	   7'h5b : foobar = {foobar, " 91"};
	   7'h5c : foobar = {foobar, " 92"};
	   7'h5d : foobar = {foobar, " 93"};
	   7'h5e : foobar = {foobar, " 94"};
	   7'h5f : foobar = {foobar, " 95"};
	   7'h60 : foobar = {foobar, " 96"};
	   7'h61 : foobar = {foobar, " 97"};
	   7'h62 : foobar = {foobar, " 98"};
	   7'h63 : foobar = {foobar, " 99"};
	   7'h64 : foobar = {foobar, " 100"};
	   7'h65 : foobar = {foobar, " 101"};
	   7'h66 : foobar = {foobar, " 102"};
	   7'h67 : foobar = {foobar, " 103"};
	   7'h68 : foobar = {foobar, " 104"};
	   7'h69 : foobar = {foobar, " 105"};
	   7'h6a : foobar = {foobar, " 106"};
	   7'h6b : foobar = {foobar, " 107"};
	   7'h6c : foobar = {foobar, " 108"};
	   7'h6d : foobar = {foobar, " 109"};
	   7'h6e : foobar = {foobar, " 110"};
	   7'h6f : foobar = {foobar, " 111"};
	   7'h70 : foobar = {foobar, " 112"};
	   7'h71 : foobar = {foobar, " 113"};
	   7'h72 : foobar = {foobar, " 114"};
	   7'h73 : foobar = {foobar, " 115"};
	   7'h74 : foobar = {foobar, " 116"};
	   7'h75 : foobar = {foobar, " 117"};
	   7'h76 : foobar = {foobar, " 118"};
	   7'h77 : foobar = {foobar, " 119"};
	   7'h78 : foobar = {foobar, " 120"};
	   7'h79 : foobar = {foobar, " 121"};
	   7'h7a : foobar = {foobar, " 122"};
	   7'h7b : foobar = {foobar, " 123"};
	   7'h7c : foobar = {foobar, " 124"};
	   7'h7d : foobar = {foobar, " 125"};
	   7'h7e : foobar = {foobar, " 126"};
	   7'h7f : foobar = {foobar, " 127"};
	   default:foobar = {foobar, " 128"};
	 endcase
      end

   endtask

   task ozonerb;
      input  [5:0] rb;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (rb[5:0])
	   6'h10,
	     6'h17,
	     6'h1e,
	     6'h1f:   foobar = {foobar, " 129"};
	   default: ozonerab({1'b1, rb}, foobar);
	 endcase
      end
   endtask

   task ozonef3f4_iext;
      input  [1:0] foo;
      input [15:0]  im16;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo)
	   2'h0 :
             begin
		skyway({4{im16[15]}}, foobar);
		skyway({4{im16[15]}}, foobar);
		skyway(im16[15:12], foobar);
		skyway(im16[11: 8], foobar);
		skyway(im16[ 7: 4], foobar);
		skyway(im16[ 3:0], foobar);
		foobar = {foobar, " 130"};
             end
	   2'h1 :
             begin
		foobar = {foobar, " 131"};
		skyway(im16[15:12], foobar);
		skyway(im16[11: 8], foobar);
		skyway(im16[ 7: 4], foobar);
		skyway(im16[ 3:0], foobar);
             end
	   2'h2 :
             begin
		skyway({4{im16[15]}}, foobar);
		skyway({4{im16[15]}}, foobar);
		skyway(im16[15:12], foobar);
		skyway(im16[11: 8], foobar);
		skyway(im16[ 7: 4], foobar);
		skyway(im16[ 3:0], foobar);
		foobar = {foobar, " 132"};
             end
	   2'h3 :
             begin
		foobar = {foobar, " 133"};
		skyway(im16[15:12], foobar);
		skyway(im16[11: 8], foobar);
		skyway(im16[ 7: 4], foobar);
		skyway(im16[ 3:0], foobar);
             end
	 endcase
      end
   endtask

   task skyway;
      input  [ 3:0] hex;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (hex)
	   4'h0 : foobar = {foobar, " 134"};
	   4'h1 : foobar = {foobar, " 135"};
	   4'h2 : foobar = {foobar, " 136"};
	   4'h3 : foobar = {foobar, " 137"};
	   4'h4 : foobar = {foobar, " 138"};
	   4'h5 : foobar = {foobar, " 139"};
	   4'h6 : foobar = {foobar, " 140"};
	   4'h7 : foobar = {foobar, " 141"};
	   4'h8 : foobar = {foobar, " 142"};
	   4'h9 : foobar = {foobar, " 143"};
	   4'ha : foobar = {foobar, " 144"};
	   4'hb : foobar = {foobar, " 145"};
	   4'hc : foobar = {foobar, " 146"};
	   4'hd : foobar = {foobar, " 147"};
	   4'he : foobar = {foobar, " 148"};
	   4'hf : foobar = {foobar, " 149"};
	 endcase
      end
   endtask

   task ozonesr;
      input  [  15:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[11: 9])
	   3'h0 : foobar = {foobar, " 158"};
	   3'h1 : foobar = {foobar, " 159"};
	   3'h2 : foobar = {foobar, " 160"};
	   3'h3 : foobar = {foobar, " 161"};
	   3'h4 : foobar = {foobar, " 162"};
	   3'h5 : foobar = {foobar, " 163"};
	   3'h6 : foobar = {foobar, " 164"};
	   3'h7 : foobar = {foobar, " 165"};
	 endcase
      end
   endtask

   task ozonejk;
      input  k;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 if (k)
	   foobar = {foobar, " 166"};
	 else
	   foobar = {foobar, " 167"};
      end
   endtask

   task ozoneae;
      input  [   2:0]   ae;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (ae)
	   3'b000 : foobar = {foobar, " 168"};
	   3'b001 : foobar = {foobar, " 169"};
	   3'b010 : foobar = {foobar, " 170"};
	   3'b011 : foobar = {foobar, " 171"};
	   3'b100 : foobar = {foobar, " 172"};
	   3'b101 : foobar = {foobar, " 173"};
	   3'b110 : foobar = {foobar, " 174"};
	   3'b111 : foobar = {foobar, " 175"};
	 endcase
      end
   endtask

   task ozoneaee;
      input  [   2:0]   aee;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (aee)
	   3'b001,
	     3'b011,
	     3'b101,
	     3'b111 : foobar = {foobar, " 176"};
	   3'b000 : foobar = {foobar, " 177"};
	   3'b010 : foobar = {foobar, " 178"};
	   3'b100 : foobar = {foobar, " 179"};
	   3'b110 : foobar = {foobar, " 180"};
	 endcase
      end
   endtask

   task ozoneape;
      input  [   2:0]   ape;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (ape)
	   3'b001,
	     3'b011,
	     3'b101,
	     3'b111 : foobar = {foobar, " 181"};
	   3'b000 : foobar = {foobar, " 182"};
	   3'b010 : foobar = {foobar, " 183"};
	   3'b100 : foobar = {foobar, " 184"};
	   3'b110 : foobar = {foobar, " 185"};
	 endcase
      end
   endtask

   task ozonef1;
      input [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[24:21])
	   4'h0 :
             if (foo[26])
               foobar = {foobar, " 186"};
             else
               foobar = {foobar, " 187"};
	   4'h1 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 188"};
               2'b01 :  foobar = {foobar, " 189"};
               2'b10 :  foobar = {foobar, " 190"};
               2'b11 :  foobar = {foobar, " 191"};
             endcase
	   4'h2 :  foobar = {foobar, " 192"};
	   4'h3 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 193"};
               2'b01 :  foobar = {foobar, " 194"};
               2'b10 :  foobar = {foobar, " 195"};
               2'b11 :  foobar = {foobar, " 196"};
             endcase
	   4'h4 :
             if (foo[26])
               foobar = {foobar, " 197"};
             else
               foobar = {foobar, " 198"};
	   4'h5 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 199"};
               2'b01 :  foobar = {foobar, " 200"};
               2'b10 :  foobar = {foobar, " 201"};
               2'b11 :  foobar = {foobar, " 202"};
             endcase
	   4'h6 :  foobar = {foobar, " 203"};
	   4'h7 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 204"};
               2'b01 :  foobar = {foobar, " 205"};
               2'b10 :  foobar = {foobar, " 206"};
               2'b11 :  foobar = {foobar, " 207"};
             endcase
	   4'h8 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 208"};
               2'b01 :  foobar = {foobar, " 209"};
               2'b10 :  foobar = {foobar, " 210"};
               2'b11 :  foobar = {foobar, " 211"};
             endcase
	   4'h9 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 212"};
               2'b01 :  foobar = {foobar, " 213"};
               2'b10 :  foobar = {foobar, " 214"};
               2'b11 :  foobar = {foobar, " 215"};
             endcase
	   4'ha :
             if (foo[25])
               foobar = {foobar, " 216"};
             else
               foobar = {foobar, " 217"};
	   4'hb :
             if (foo[25])
               foobar = {foobar, " 218"};
             else
               foobar = {foobar, " 219"};
	   4'hc :
             if (foo[26])
               foobar = {foobar, " 220"};
             else
               foobar = {foobar, " 221"};
	   4'hd :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 222"};
               2'b01 :  foobar = {foobar, " 223"};
               2'b10 :  foobar = {foobar, " 224"};
               2'b11 :  foobar = {foobar, " 225"};
             endcase
	   4'he :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 226"};
               2'b01 :  foobar = {foobar, " 227"};
               2'b10 :  foobar = {foobar, " 228"};
               2'b11 :  foobar = {foobar, " 229"};
             endcase
	   4'hf :
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 230"};
               2'b01 :  foobar = {foobar, " 231"};
               2'b10 :  foobar = {foobar, " 232"};
               2'b11 :  foobar = {foobar, " 233"};
             endcase
	 endcase
      end
   endtask

   task ozonef1e;
      input [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[27:21])
	   7'h00:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 234"};
		foobar = {foobar, " 235"};
	     end
	   7'h01:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 236"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 237"};
		foobar = {foobar, " 238"};
	     end
	   7'h02:
	     foobar = {foobar, " 239"};
	   7'h03:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 240"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 241"};
		foobar = {foobar, " 242"};
	     end
	   7'h04:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 243"};
		foobar = {foobar," 244"};
	     end
	   7'h05:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 245"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 246"};
	     end
	   7'h06:
	     foobar = {foobar, " 247"};
	   7'h07:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 248"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 249"};
	     end
	   7'h08:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 250"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 251"};
	     end
	   7'h09:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 252"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 253"};
	     end
	   7'h0a:
	     begin
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 254"};
	     end
	   7'h0b:
	     begin
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 255"};
	     end
	   7'h0c:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 256"};
	     end
	   7'h0d:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 257"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 258"};
	     end
	   7'h0e:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 259"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 260"};
	     end
	   7'h0f:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 261"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 262"};
	     end
	   7'h10:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 263"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 264"};
		foobar = {foobar, " 265"};
		foobar = {foobar, " 266"};
	     end
	   7'h11:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 267"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 268"};
		foobar = {foobar, " 269"};
		foobar = {foobar, " 270"};
	     end
	   7'h12:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 271"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 272"};
		foobar = {foobar, " 273"};
		foobar = {foobar, " 274"};
	     end
	   7'h13:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 275"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 276"};
		foobar = {foobar, " 277"};
		foobar = {foobar, " 278"};
	     end
	   7'h14:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 279"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 280"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 281"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 282"};
		foobar = {foobar, " 283"};
		foobar = {foobar, " 284"};
	     end
	   7'h15:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 285"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 286"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 287"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 288"};
		foobar = {foobar, " 289"};
		foobar = {foobar, " 290"};
	     end
	   7'h16:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 291"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 292"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 293"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 294"};
		foobar = {foobar, " 295"};
		foobar = {foobar, " 296"};
	     end
	   7'h17:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 297"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 298"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 299"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 300"};
		foobar = {foobar, " 301"};
		foobar = {foobar, " 302"};
	     end
	   7'h18:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 303"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 304"};
		foobar = {foobar, " 305"};
		foobar = {foobar, " 306"};
	     end
	   7'h19:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 307"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 308"};
		foobar = {foobar, " 309"};
		foobar = {foobar, " 310"};
	     end
	   7'h1a:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 311"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 312"};
		foobar = {foobar, " 313"};
		foobar = {foobar, " 314"};
	     end
	   7'h1b:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 315"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 316"};
		foobar = {foobar, " 317"};
		foobar = {foobar, " 318"};
	     end
	   7'h1c:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 319"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 320"};
		foobar = {foobar, " 321"};
		foobar = {foobar, " 322"};
	     end
	   7'h1d:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 323"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 324"};
		foobar = {foobar, " 325"};
		foobar = {foobar, " 326"};
	     end
	   7'h1e:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 327"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 328"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 329"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 330"};
		foobar = {foobar, " 331"};
		foobar = {foobar, " 332"};
	     end
	   7'h1f:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 333"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 334"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 335"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 336"};
		foobar = {foobar, " 337"};
		foobar = {foobar, " 338"};
	     end
	   7'h20:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 339"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 340"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 341"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 342"};
		foobar = {foobar, " 343"};
		foobar = {foobar, " 344"};
	     end
	   7'h21:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 345"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 346"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 347"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 348"};
		foobar = {foobar, " 349"};
		foobar = {foobar, " 350"};
	     end
	   7'h22:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 351"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 352"};
		foobar = {foobar, " 353"};
		foobar = {foobar, " 354"};
	     end
	   7'h23:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 355"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 356"};
		foobar = {foobar, " 357"};
		foobar = {foobar, " 358"};
	     end
	   7'h24:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 359"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 360"};
		foobar = {foobar, " 361"};
		foobar = {foobar, " 362"};
	     end
	   7'h25:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 363"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 364"};
		foobar = {foobar, " 365"};
		foobar = {foobar, " 366"};
	     end
	   7'h26:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 367"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 368"};
		foobar = {foobar, " 369"};
		foobar = {foobar, " 370"};
	     end
	   7'h27:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 371"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 372"};
		foobar = {foobar, " 373"};
		foobar = {foobar, " 374"};
	     end
	   7'h28:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 375"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 376"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 377"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 378"};
		foobar = {foobar, " 379"};
		foobar = {foobar, " 380"};
	     end
	   7'h29:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 381"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 382"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 383"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 384"};
		foobar = {foobar, " 385"};
		foobar = {foobar, " 386"};
	     end
	   7'h2a:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 387"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 388"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 389"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 390"};
		foobar = {foobar, " 391"};
		foobar = {foobar, " 392"};
	     end
	   7'h2b:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 393"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 394"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 395"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 396"};
		foobar = {foobar, " 397"};
		foobar = {foobar, " 398"};
	     end
	   7'h2c:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 399"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 400"};
		foobar = {foobar, " 401"};
		foobar = {foobar, " 402"};
	     end
	   7'h2d:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 403"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 404"};
		foobar = {foobar, " 405"};
		foobar = {foobar, " 406"};
	     end
	   7'h2e:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 407"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 408"};
		foobar = {foobar, " 409"};
		foobar = {foobar, " 410"};
	     end
	   7'h2f:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 411"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 412"};
		foobar = {foobar, " 413"};
		foobar = {foobar, " 414"};
	     end
	   7'h30:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 415"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 416"};
		foobar = {foobar, " 417"};
		foobar = {foobar, " 418"};
	     end
	   7'h31:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 419"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 420"};
		foobar = {foobar, " 421"};
		foobar = {foobar, " 422"};
	     end
	   7'h32:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 423"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 424"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 425"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 426"};
		foobar = {foobar, " 427"};
		foobar = {foobar, " 428"};
	     end
	   7'h33:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 429"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 430"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 431"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 432"};
		foobar = {foobar, " 433"};
		foobar = {foobar, " 434"};
	     end
	   7'h34:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 435"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 436"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 437"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 438"};
		foobar = {foobar, " 439"};
		foobar = {foobar, " 440"};
	     end
	   7'h35:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 441"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 442"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 443"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 444"};
		foobar = {foobar, " 445"};
		foobar = {foobar, " 446"};
	     end
	   7'h36:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 447"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 448"};
		foobar = {foobar, " 449"};
		foobar = {foobar, " 450"};
	     end
	   7'h37:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 451"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 452"};
		foobar = {foobar, " 453"};
		foobar = {foobar, " 454"};
	     end
	   7'h38:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 455"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 456"};
		foobar = {foobar, " 457"};
	     end
	   7'h39:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 458"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 459"};
		foobar = {foobar, " 460"};
	     end
	   7'h3a:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 461"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 462"};
		foobar = {foobar, " 463"};
	     end
	   7'h3b:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 464"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 465"};
		foobar = {foobar, " 466"};
	     end
	   7'h3c:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 467"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 468"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 469"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 470"};
		foobar = {foobar, " 471"};
	     end
	   7'h3d:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 472"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 473"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 474"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 475"};
		foobar = {foobar, " 476"};
	     end
	   7'h3e:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 477"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 478"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 479"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 480"};
		foobar = {foobar, " 481"};
	     end
	   7'h3f:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 482"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 483"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 484"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 485"};
		foobar = {foobar, " 486"};
	     end
	   7'h40:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 487"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 488"};
		foobar = {foobar, " 489"};
		foobar = {foobar, " 490"};
	     end
	   7'h41:
	     begin
		foobar = {foobar, " 491"};
		foobar = {foobar, " 492"};
	     end
	   7'h42:
	     begin
		foobar = {foobar, " 493"};
		foobar = {foobar, " 494"};
	     end
	   7'h43:
	     begin
		foobar = {foobar, " 495"};
		foobar = {foobar, " 496"};
	     end
	   7'h44:
	     begin
		foobar = {foobar, " 497"};
		foobar = {foobar, " 498"};
	     end
	   7'h45:
	     foobar = {foobar, " 499"};
	   7'h46:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 500"};
		foobar = {foobar, " 501"};
		foobar = {foobar, " 502"};
	     end
	   7'h47:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 503"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 504"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 505"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 506"};
		foobar = {foobar, " 507"};
		foobar = {foobar, " 508"};
	     end
	   7'h48:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 509"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 510"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 511"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 512"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 513"};
	     end
	   7'h49:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 514"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 515"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 516"};
	     end
	   7'h4a:
             foobar = {foobar," 517"};
	   7'h4b:
             foobar = {foobar, " 518"};
	   7'h4c:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 519"};
		foobar = {foobar, " 520"};
		foobar = {foobar, " 521"};
	     end
	   7'h4d:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 522"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 523"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 524"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 525"};
		foobar = {foobar, " 526"};
		foobar = {foobar, " 527"};
	     end
	   7'h4e:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 528"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 529"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 530"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 531"};
	     end
	   7'h4f:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 532"};
	     end
	   7'h50:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 533"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 534"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 535"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 536"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 537"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 538"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 539"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 540"};
	     end
	   7'h51:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 541"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 542"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 543"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 544"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 545"};
	     end
	   7'h52:
	     foobar = {foobar, " 546"};
	   7'h53:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar, " 547"};
	     end
	   7'h54:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 548"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 549"};
	     end
	   7'h55:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 550"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 551"};
	     end
	   7'h56:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 552"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 553"};
		foobar = {foobar, " 554"};
	     end
	   7'h57:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 555"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 556"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 557"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 558"};
	     end
	   7'h58:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar, " 559"};
	     end
	   7'h59:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 560"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 561"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 562"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 563"};
	     end
	   7'h5a:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 564"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar, " 565"};
	     end
	   7'h5b:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 566"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar, " 567"};
	     end
	   7'h5c:
	     begin
		foobar = {foobar," 568"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 569"};
		foobar = {foobar," 570"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 571"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 572"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar, " 573"};
	     end
	   7'h5d:
	     begin
		foobar = {foobar," 574"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 575"};
		foobar = {foobar," 576"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 577"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 578"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar, " 579"};
	     end
	   7'h5e:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 580"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar, " 581"};
	     end
	   7'h5f:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 582"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 583"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 584"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 585"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 586"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 587"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 588"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 589"};
	     end
	   7'h60:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 590"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 591"};
	     end
	   7'h61:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 592"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 593"};
	     end
	   7'h62:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 594"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 595"};
	     end
	   7'h63:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 596"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 597"};
	     end
	   7'h64:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 598"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 599"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 600"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 601"};
	     end
	   7'h65:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 602"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 603"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 604"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 605"};
	     end
	   7'h66:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 606"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 607"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 608"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 609"};
	     end
	   7'h67:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 610"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 611"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 612"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 613"};
	     end
	   7'h68:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 614"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 615"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 616"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 617"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 618"};
		ozoneape(foo[17:15], foobar);
	     end
	   7'h69:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 619"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 620"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 621"};
	     end
	   7'h6a:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 622"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 623"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 624"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 625"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 626"};
		ozoneae(foo[17:15], foobar);
	     end
	   7'h6b:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 627"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 628"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 629"};
	     end
	   7'h6c:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 630"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 631"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 632"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 633"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 634"};
		ozoneae(foo[17:15], foobar);
	     end
	   7'h6d:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 635"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 636"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 637"};
	     end
	   7'h6e:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 638"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 639"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 640"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 641"};
	     end
	   7'h6f:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 642"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 643"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 644"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 645"};
	     end
	   7'h70:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 646"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 647"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 648"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar, " 649"};
	     end
	   7'h71:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 650"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar, " 651"};
	     end
	   7'h72:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 652"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar, " 653"};
	     end
	   7'h73:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 654"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 655"};
		ozoneae(foo[17:15], foobar);
	     end
	   7'h74:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 656"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 657"};
		ozoneae(foo[17:15], foobar);
	     end
	   7'h75:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 658"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 659"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 660"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 661"};
		foobar = {foobar, " 662"};
		foobar = {foobar, " 663"};
	     end
	   7'h76:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 664"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 665"};
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 666"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 667"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 668"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 669"};
	     end
	   7'h77:
	     begin
		ozoneaee(foo[20:18], foobar);
		foobar = {foobar," 670"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 671"};
		ozoneaee(foo[17:15], foobar);
		foobar = {foobar," 672"};
		ozoneape(foo[20:18], foobar);
		foobar = {foobar," 673"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 674"};
		ozoneape(foo[17:15], foobar);
		foobar = {foobar," 675"};
	     end
	   7'h78,
	     7'h79,
	     7'h7a,
	     7'h7b,
	     7'h7c,
	     7'h7d,
	     7'h7e,
	     7'h7f:
               foobar = {foobar," 676"};
	 endcase
      end
   endtask

   task ozonef2;
      input [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[24:21])
	   4'h0 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 677"};
               2'b01 :  foobar = {foobar," 678"};
               2'b10 :  foobar = {foobar," 679"};
               2'b11 :  foobar = {foobar," 680"};
             endcase
	   4'h1 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 681"};
               2'b01 :  foobar = {foobar," 682"};
               2'b10 :  foobar = {foobar," 683"};
               2'b11 :  foobar = {foobar," 684"};
             endcase
	   4'h2 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 685"};
               2'b01 :  foobar = {foobar," 686"};
               2'b10 :  foobar = {foobar," 687"};
               2'b11 :  foobar = {foobar," 688"};
             endcase
	   4'h3 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 689"};
               2'b01 :  foobar = {foobar," 690"};
               2'b10 :  foobar = {foobar," 691"};
               2'b11 :  foobar = {foobar," 692"};
             endcase
	   4'h4 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 693"};
               2'b01 :  foobar = {foobar," 694"};
               2'b10 :  foobar = {foobar," 695"};
               2'b11 :  foobar = {foobar," 696"};
             endcase
	   4'h5 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 697"};
               2'b01 :  foobar = {foobar," 698"};
               2'b10 :  foobar = {foobar," 699"};
               2'b11 :  foobar = {foobar," 700"};
             endcase
	   4'h6 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 701"};
               2'b01 :  foobar = {foobar," 702"};
               2'b10 :  foobar = {foobar," 703"};
               2'b11 :  foobar = {foobar," 704"};
             endcase
	   4'h7 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 705"};
               2'b01 :  foobar = {foobar," 706"};
               2'b10 :  foobar = {foobar," 707"};
               2'b11 :  foobar = {foobar," 708"};
             endcase
	   4'h8 :
             if (foo[26])
               foobar = {foobar," 709"};
             else
               foobar = {foobar," 710"};
	   4'h9 :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 711"};
               2'b01 :  foobar = {foobar," 712"};
               2'b10 :  foobar = {foobar," 713"};
               2'b11 :  foobar = {foobar," 714"};
             endcase
	   4'ha :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 715"};
               2'b01 :  foobar = {foobar," 716"};
               2'b10 :  foobar = {foobar," 717"};
               2'b11 :  foobar = {foobar," 718"};
             endcase
	   4'hb :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 719"};
               2'b01 :  foobar = {foobar," 720"};
               2'b10 :  foobar = {foobar," 721"};
               2'b11 :  foobar = {foobar," 722"};
             endcase
	   4'hc :
             if (foo[26])
               foobar = {foobar," 723"};
             else
               foobar = {foobar," 724"};
	   4'hd :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 725"};
               2'b01 :  foobar = {foobar," 726"};
               2'b10 :  foobar = {foobar," 727"};
               2'b11 :  foobar = {foobar," 728"};
             endcase
	   4'he :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 729"};
               2'b01 :  foobar = {foobar," 730"};
               2'b10 :  foobar = {foobar," 731"};
               2'b11 :  foobar = {foobar," 732"};
             endcase
	   4'hf :
             case (foo[26:25])
               2'b00 :  foobar = {foobar," 733"};
               2'b01 :  foobar = {foobar," 734"};
               2'b10 :  foobar = {foobar," 735"};
               2'b11 :  foobar = {foobar," 736"};
             endcase
	 endcase
      end
   endtask

   task ozonef2e;
      input [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 casez (foo[25:21])
	   5'h00 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 737"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 738"};
	     end
	   5'h01 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 739"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 740"};
	     end
	   5'h02 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 741"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 742"};
	     end
	   5'h03 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 743"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 744"};
	     end
	   5'h04 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 745"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 746"};
	     end
	   5'h05 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 747"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 748"};
	     end
	   5'h06 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 749"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 750"};
	     end
	   5'h07 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 751"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 752"};
	     end
	   5'h08 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 753"};
		if (foo[ 6])
		  foobar = {foobar," 754"};
		else
		  foobar = {foobar," 755"};
	     end
	   5'h09 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 756"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 757"};
	     end
	   5'h0a :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 758"};
		ozoneae(foo[17:15], foobar);
	     end
	   5'h0b :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 759"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 760"};
	     end
	   5'h0c :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 761"};
	     end
	   5'h0d :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 762"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 763"};
	     end
	   5'h0e :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 764"};
		ozoneae(foo[17:15], foobar);
	     end
	   5'h0f :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 765"};
		ozoneae(foo[17:15], foobar);
	     end
	   5'h10 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 766"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 767"};
	     end
	   5'h11 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 768"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 769"};
	     end
	   5'h18 :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 770"};
		if (foo[ 6])
		  foobar = {foobar," 771"};
		else
		  foobar = {foobar," 772"};
	     end
	   5'h1a :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 773"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 774"};
	     end
	   5'h1b :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 775"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 776"};
		if (foo[ 6])
		  foobar = {foobar," 777"};
		else
		  foobar = {foobar," 778"};
		foobar = {foobar," 779"};
	     end
	   5'h1c :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 780"};
	     end
	   5'h1d :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 781"};
		if (foo[ 6])
		  foobar = {foobar," 782"};
		else
		  foobar = {foobar," 783"};
		foobar = {foobar," 784"};
	     end
	   5'h1e :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 785"};
		if (foo[ 6])
		  foobar = {foobar," 786"};
		else
		  foobar = {foobar," 787"};
		foobar = {foobar," 788"};
	     end
	   5'h1f :
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 789"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 790"};
		if (foo[ 6])
		  foobar = {foobar," 791"};
		else
		  foobar = {foobar," 792"};
		foobar = {foobar," 793"};
	     end
	   default :
             foobar = {foobar," 794"};
	 endcase
      end
   endtask

   task ozonef3e;
      input [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[25:21])
	   5'h00,
	     5'h01,
	     5'h02:
	       begin
		  ozoneae(foo[20:18], foobar);
		  case (foo[22:21])
		    2'h0: foobar = {foobar," 795"};
		    2'h1: foobar = {foobar," 796"};
		    2'h2: foobar = {foobar," 797"};
		  endcase
		  ozoneae(foo[17:15], foobar);
		  foobar = {foobar," 798"};
		  if (foo[ 9])
		    ozoneae(foo[ 8: 6], foobar);
		  else
		    ozonef3e_te(foo[ 8: 6], foobar);
		  foobar = {foobar," 799"};
	       end
	   5'h08,
	     5'h09,
	     5'h0d,
	     5'h0e,
	     5'h0f:
	       begin
		  ozoneae(foo[20:18], foobar);
		  foobar = {foobar," 800"};
		  ozoneae(foo[17:15], foobar);
		  case (foo[23:21])
		    3'h0: foobar = {foobar," 801"};
		    3'h1: foobar = {foobar," 802"};
		    3'h5: foobar = {foobar," 803"};
		    3'h6: foobar = {foobar," 804"};
		    3'h7: foobar = {foobar," 805"};
		  endcase
		  if (foo[ 9])
		    ozoneae(foo[ 8: 6], foobar);
		  else
		    ozonef3e_te(foo[ 8: 6], foobar);
	       end
	   5'h0a,
	     5'h0b:
	       begin
		  ozoneae(foo[17:15], foobar);
		  if (foo[21])
		    foobar = {foobar," 806"};
		  else
		    foobar = {foobar," 807"};
		  if (foo[ 9])
		    ozoneae(foo[ 8: 6], foobar);
		  else
		    ozonef3e_te(foo[ 8: 6], foobar);
	       end
	   5'h0c:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 808"};
		if (foo[ 9])
		  ozoneae(foo[ 8: 6], foobar);
		else
		  ozonef3e_te(foo[ 8: 6], foobar);
		foobar = {foobar," 809"};
		ozoneae(foo[17:15], foobar);
	     end
	   5'h10,
	     5'h11,
	     5'h12,
	     5'h13:
	       begin
		  ozoneae(foo[20:18], foobar);
		  foobar = {foobar," 810"};
		  ozoneae(foo[17:15], foobar);
		  case (foo[22:21])
		    2'h0,
		      2'h2:
			foobar = {foobar," 811"};
		    2'h1,
		      2'h3:
			foobar = {foobar," 812"};
		  endcase
		  ozoneae(foo[ 8: 6], foobar);
		  foobar = {foobar," 813"};
		  ozoneae((foo[20:18]+1), foobar);
		  foobar = {foobar," 814"};
		  ozoneae((foo[17:15]+1), foobar);
		  case (foo[22:21])
		    2'h0,
		      2'h3:
			foobar = {foobar," 815"};
		    2'h1,
		      2'h2:
			foobar = {foobar," 816"};
		  endcase
		  ozoneae((foo[ 8: 6]+1), foobar);
	       end
	   5'h18:
	     begin
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 817"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 818"};
		ozoneae(foo[ 8: 6], foobar);
		foobar = {foobar," 819"};
		ozoneae(foo[20:18], foobar);
		foobar = {foobar," 820"};
		ozoneae(foo[17:15], foobar);
		foobar = {foobar," 821"};
		ozoneae(foo[ 8: 6], foobar);
	     end
	   default :
             foobar = {foobar," 822"};
	 endcase
      end
   endtask
   task ozonef3e_te;
      input  [   2:0]   te;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (te)
	   3'b100 : foobar = {foobar, " 823"};
	   3'b101 : foobar = {foobar, " 824"};
	   3'b110 : foobar = {foobar, " 825"};
	   default: foobar = {foobar, " 826"};
	 endcase
      end
   endtask
   task ozonearm;
      input  [   2:0]   ate;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (ate)
	   3'b000 : foobar = {foobar, " 827"};
	   3'b001 : foobar = {foobar, " 828"};
	   3'b010 : foobar = {foobar, " 829"};
	   3'b011 : foobar = {foobar, " 830"};
	   3'b100 : foobar = {foobar, " 831"};
	   3'b101 : foobar = {foobar, " 832"};
	   3'b110 : foobar = {foobar, " 833"};
	   3'b111 : foobar = {foobar, " 834"};
	 endcase
      end
   endtask
   task ozonebmuop;
      input  [ 4:0] f4;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (f4[ 4:0])
	   5'h00,
	     5'h04 :
               foobar = {foobar, " 835"};
	   5'h01,
	     5'h05 :
               foobar = {foobar, " 836"};
	   5'h02,
	     5'h06 :
               foobar = {foobar, " 837"};
	   5'h03,
	     5'h07 :
               foobar = {foobar, " 838"};
	   5'h08,
	     5'h18 :
               foobar = {foobar, " 839"};
	   5'h09,
	     5'h19 :
               foobar = {foobar, " 840"};
	   5'h0a,
	     5'h1a :
               foobar = {foobar, " 841"};
	   5'h0b :
             foobar = {foobar, " 842"};
	   5'h1b :
             foobar = {foobar, " 843"};
	   5'h0c,
	     5'h1c :
               foobar = {foobar, " 844"};
	   5'h0d,
	     5'h1d :
               foobar = {foobar, " 845"};
	   5'h1e :
             foobar = {foobar, " 846"};
	 endcase
      end
   endtask
   task ozonef3;
      input  [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      reg 		  nacho;
      // verilator no_inline_task
      begin : f3_body
	 nacho = 1'b0;
	 case (foo[24:21])
	   4'h0:
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 847"};
               2'b01 :  foobar = {foobar, " 848"};
               2'b10 :  foobar = {foobar, " 849"};
               2'b11 :  foobar = {foobar, " 850"};
             endcase
	   4'h1:
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 851"};
               2'b01 :  foobar = {foobar, " 852"};
               2'b10 :  foobar = {foobar, " 853"};
               2'b11 :  foobar = {foobar, " 854"};
             endcase
	   4'h2:
             case (foo[26:25])
               2'b00 :  foobar = {foobar, " 855"};
               2'b01 :  foobar = {foobar, " 856"};
               2'b10 :  foobar = {foobar, " 857"};
               2'b11 :  foobar = {foobar, " 858"};
             endcase
	   4'h8,
	     4'h9,
	     4'hd,
	     4'he,
	     4'hf :
               case (foo[26:25])
		 2'b00 :  foobar = {foobar, " 859"};
		 2'b01 :  foobar = {foobar, " 860"};
		 2'b10 :  foobar = {foobar, " 861"};
		 2'b11 :  foobar = {foobar, " 862"};
               endcase
	   4'ha,
	     4'hb :
               if (foo[25])
		 foobar = {foobar, " 863"};
               else
		 foobar = {foobar, " 864"};
	   4'hc :
             if (foo[26])
               foobar = {foobar, " 865"};
             else
               foobar = {foobar, " 866"};
	   default :
	     begin
		foobar = {foobar, " 867"};
		nacho = 1'b1;
	     end
	 endcase
	 if (~nacho)
	   begin
	      case (foo[24:21])
		4'h8 :
		  foobar = {foobar, " 868"};
		4'h9 :
		  foobar = {foobar, " 869"};
		4'ha,
		  4'he :
		    foobar = {foobar, " 870"};
		4'hb,
		  4'hf :
		    foobar = {foobar, " 871"};
		4'hd :
		  foobar = {foobar, " 872"};
	      endcase
	      if (foo[20])
		case (foo[18:16])
		  3'b000 : foobar = {foobar, " 873"};
		  3'b100 : foobar = {foobar, " 874"};
		  default: foobar = {foobar, " 875"};
		endcase
	      else
		ozoneae(foo[18:16], foobar);
	      if (foo[24:21] === 4'hc)
		if (foo[25])
		  foobar = {foobar, " 876"};
		else
		  foobar = {foobar, " 877"};
	      case (foo[24:21])
		4'h0,
		  4'h1,
		  4'h2:
		    foobar = {foobar, " 878"};
	      endcase
	   end
      end
   endtask
   task ozonerx;
      input  [  31:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[19:18])
	   2'h0 :  foobar = {foobar, " 879"};
	   2'h1 :  foobar = {foobar, " 880"};
	   2'h2 :  foobar = {foobar, " 881"};
	   2'h3 :  foobar = {foobar, " 882"};
	 endcase
	 case (foo[17:16])
	   2'h1 :  foobar = {foobar, " 883"};
	   2'h2 :  foobar = {foobar, " 884"};
	   2'h3 :  foobar = {foobar, " 885"};
	 endcase
      end
   endtask
   task ozonerme;
      input  [  2:0] rme;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (rme)
	   3'h0 :  foobar = {foobar, " 886"};
	   3'h1 :  foobar = {foobar, " 887"};
	   3'h2 :  foobar = {foobar, " 888"};
	   3'h3 :  foobar = {foobar, " 889"};
	   3'h4 :  foobar = {foobar, " 890"};
	   3'h5 :  foobar = {foobar, " 891"};
	   3'h6 :  foobar = {foobar, " 892"};
	   3'h7 :  foobar = {foobar, " 893"};
	 endcase
      end
   endtask
   task ozoneye;
      input  [5:0] ye;
      input 	      l;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 foobar = {foobar, " 894"};
	 ozonerme(ye[5:3],foobar);
	 case ({ye[ 2:0], l})
	   4'h2,
	     4'ha:  foobar = {foobar, " 895"};
	   4'h4,
	     4'hb:  foobar = {foobar, " 896"};
	   4'h6,
	     4'he:  foobar = {foobar, " 897"};
	   4'h8,
	     4'hc:  foobar = {foobar, " 898"};
	 endcase
      end
   endtask
   task ozonef1e_ye;
      input  [5:0] ye;
      input 	      l;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 foobar = {foobar, " 899"};
	 ozonerme(ye[5:3],foobar);
	 ozonef1e_inc_dec(ye[5:0], l ,foobar);
      end
   endtask
   task ozonef1e_h;
      input  [  2:0] e;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 if (e[ 2:0] <= 3'h4)
	   foobar = {foobar, " 900"};
      end
   endtask
   task ozonef1e_inc_dec;
      input  [5:0] ye;
      input 	      l;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case ({ye[ 2:0], l})
	   4'h2,
	     4'h3,
	     4'ha:  foobar = {foobar, " 901"};
	   4'h4,
	     4'h5,
	     4'hb:  foobar = {foobar, " 902"};
	   4'h6,
	     4'h7,
	     4'he:  foobar = {foobar, " 903"};
	   4'h8,
	     4'h9,
	     4'hc:  foobar = {foobar, " 904"};
	   4'hf:  foobar = {foobar, " 905"};
	 endcase
      end
   endtask
   task ozonef1e_hl;
      input  [  2:0] e;
      input           l;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case ({e[ 2:0], l})
	   4'h0,
	     4'h2,
	     4'h4,
	     4'h6,
	     4'h8: foobar = {foobar, " 906"};
	   4'h1,
	     4'h3,
	     4'h5,
	     4'h7,
	     4'h9: foobar = {foobar, " 907"};
	 endcase
      end
   endtask
   task ozonexe;
      input  [  3:0] xe;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (xe[3])
	   1'b0 :  foobar = {foobar, " 908"};
	   1'b1 :  foobar = {foobar, " 909"};
	 endcase
	 case (xe[ 2:0])
	   3'h1,
	     3'h5:  foobar = {foobar, " 910"};
	   3'h2,
	     3'h6:  foobar = {foobar, " 911"};
	   3'h3,
	     3'h7:  foobar = {foobar, " 912"};
	   3'h4:  foobar = {foobar, " 913"};
	 endcase
      end
   endtask
   task ozonerp;
      input  [  2:0] rp;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (rp)
	   3'h0 :  foobar = {foobar, " 914"};
	   3'h1 :  foobar = {foobar, " 915"};
	   3'h2 :  foobar = {foobar, " 916"};
	   3'h3 :  foobar = {foobar, " 917"};
	   3'h4 :  foobar = {foobar, " 918"};
	   3'h5 :  foobar = {foobar, " 919"};
	   3'h6 :  foobar = {foobar, " 920"};
	   3'h7 :  foobar = {foobar, " 921"};
	 endcase
      end
   endtask
   task ozonery;
      input  [  3:0] ry;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (ry)
	   4'h0 :  foobar = {foobar, " 922"};
	   4'h1 :  foobar = {foobar, " 923"};
	   4'h2 :  foobar = {foobar, " 924"};
	   4'h3 :  foobar = {foobar, " 925"};
	   4'h4 :  foobar = {foobar, " 926"};
	   4'h5 :  foobar = {foobar, " 927"};
	   4'h6 :  foobar = {foobar, " 928"};
	   4'h7 :  foobar = {foobar, " 929"};
	   4'h8 :  foobar = {foobar, " 930"};
	   4'h9 :  foobar = {foobar, " 931"};
	   4'ha :  foobar = {foobar, " 932"};
	   4'hb :  foobar = {foobar, " 933"};
	   4'hc :  foobar = {foobar, " 934"};
	   4'hd :  foobar = {foobar, " 935"};
	   4'he :  foobar = {foobar, " 936"};
	   4'hf :  foobar = {foobar, " 937"};
	 endcase
      end
   endtask
   task ozonearx;
      input  [  15:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[1:0])
	   2'h0 :  foobar = {foobar, " 938"};
	   2'h1 :  foobar = {foobar, " 939"};
	   2'h2 :  foobar = {foobar, " 940"};
	   2'h3 :  foobar = {foobar, " 941"};
	 endcase
      end
   endtask
   task ozonef3f4imop;
      input  [  4:0]   f3f4iml;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 casez (f3f4iml)
	   5'b000??: foobar = {foobar, " 942"};
	   5'b001??: foobar = {foobar, " 943"};
	   5'b?10??: foobar = {foobar, " 944"};
	   5'b0110?: foobar = {foobar, " 945"};
	   5'b01110: foobar = {foobar, " 946"};
	   5'b01111: foobar = {foobar, " 947"};
	   5'b10???: foobar = {foobar, " 948"};
	   5'b11100: foobar = {foobar, " 949"};
	   5'b11101: foobar = {foobar, " 950"};
	   5'b11110: foobar = {foobar, " 951"};
	   5'b11111: foobar = {foobar, " 952"};
	 endcase
      end
   endtask
   task ozonecon;
      input  [  4:0] con;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (con)
	   5'h00 :  foobar = {foobar, " 953"};
	   5'h01 :  foobar = {foobar, " 954"};
	   5'h02 :  foobar = {foobar, " 955"};
	   5'h03 :  foobar = {foobar, " 956"};
	   5'h04 :  foobar = {foobar, " 957"};
	   5'h05 :  foobar = {foobar, " 958"};
	   5'h06 :  foobar = {foobar, " 959"};
	   5'h07 :  foobar = {foobar, " 960"};
	   5'h08 :  foobar = {foobar, " 961"};
	   5'h09 :  foobar = {foobar, " 962"};
	   5'h0a :  foobar = {foobar, " 963"};
	   5'h0b :  foobar = {foobar, " 964"};
	   5'h0c :  foobar = {foobar, " 965"};
	   5'h0d :  foobar = {foobar, " 966"};
	   5'h0e :  foobar = {foobar, " 967"};
	   5'h0f :  foobar = {foobar, " 968"};
	   5'h10 :  foobar = {foobar, " 969"};
	   5'h11 :  foobar = {foobar, " 970"};
	   5'h12 :  foobar = {foobar, " 971"};
	   5'h13 :  foobar = {foobar, " 972"};
	   5'h14 :  foobar = {foobar, " 973"};
	   5'h15 :  foobar = {foobar, " 974"};
	   5'h16 :  foobar = {foobar, " 975"};
	   5'h17 :  foobar = {foobar, " 976"};
	   5'h18 :  foobar = {foobar, " 977"};
	   5'h19 :  foobar = {foobar, " 978"};
	   5'h1a :  foobar = {foobar, " 979"};
	   5'h1b :  foobar = {foobar, " 980"};
	   5'h1c :  foobar = {foobar, " 981"};
	   5'h1d :  foobar = {foobar, " 982"};
	   5'h1e :  foobar = {foobar, " 983"};
	   5'h1f :  foobar = {foobar, " 984"};
	 endcase
      end
   endtask
   task ozonedr;
      input  [  15:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[ 9: 6])
	   4'h0 :  foobar = {foobar, " 985"};
	   4'h1 :  foobar = {foobar, " 986"};
	   4'h2 :  foobar = {foobar, " 987"};
	   4'h3 :  foobar = {foobar, " 988"};
	   4'h4 :  foobar = {foobar, " 989"};
	   4'h5 :  foobar = {foobar, " 990"};
	   4'h6 :  foobar = {foobar, " 991"};
	   4'h7 :  foobar = {foobar, " 992"};
	   4'h8 :  foobar = {foobar, " 993"};
	   4'h9 :  foobar = {foobar, " 994"};
	   4'ha :  foobar = {foobar, " 995"};
	   4'hb :  foobar = {foobar, " 996"};
	   4'hc :  foobar = {foobar, " 997"};
	   4'hd :  foobar = {foobar, " 998"};
	   4'he :  foobar = {foobar, " 999"};
	   4'hf :  foobar = {foobar, " 1000"};
	 endcase
      end
   endtask
   task ozoneshift;
      input  [  15:0] foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo[ 4: 3])
	   2'h0 :  foobar = {foobar, " 1001"};
	   2'h1 :  foobar = {foobar, " 1002"};
	   2'h2 :  foobar = {foobar, " 1003"};
	   2'h3 :  foobar = {foobar, " 1004"};
	 endcase
      end
   endtask
   task ozoneacc;
      input            foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo)
	   2'h0 :  foobar = {foobar, " 1005"};
	   2'h1 :  foobar = {foobar, " 1006"};
	 endcase
      end
   endtask
   task ozonehl;
      input            foo;
      inout [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 case (foo)
	   2'h0 :  foobar = {foobar, " 1007"};
	   2'h1 :  foobar = {foobar, " 1008"};
	 endcase
      end
   endtask
   task dude;
      inout  [STRLEN*8: 1] foobar;
      reg [   7:0] 	   temp;
      integer 		   i;
      reg 		   nacho;
      // verilator no_inline_task
      begin : justify_block
	 nacho = 1'b0;
	 for (i=STRLEN-1; i>1; i=i-1)
	   begin
	      temp = foobar>>((STRLEN-1)*8);
	      if (temp || nacho)
		nacho = 1'b1;
	      else
		begin
		   foobar = foobar<<8;
		   foobar[8:1] = 32;
		end
	   end
      end
   endtask

   task big_case;
      input  [  31:0] fd;
      input [  31:0]  foo;
      reg [STRLEN*8: 1] foobar;
      // verilator no_inline_task
      begin
	 foobar = " 1009";
	 if (&foo === 1'bx)
	   $fwrite(fd, " 1010");
	 else
	   casez ( {foo[31:26], foo[19:15], foo[5:0]} )
             17'b00_111?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1011"};
		  ozoneacc(~foo[26], foobar);
		  ozonehl(foo[20], foobar);
		  foobar = {foobar, " 1012"};
		  ozonerx(foo, foobar);
		  dude(foobar);
		  $fwrite (fd, " 1013:%s", foobar);
               end
             17'b01_001?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1014"};
		  ozonerx(foo, foobar);
		  foobar = {foobar, " 1015"};
		  foobar = {foobar, " 1016"};
		  ozonehl(foo[20], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1017:%s", foobar);
               end
             17'b10_100?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1018"};
		  ozonerx(foo, foobar);
		  foobar = {foobar, " 1019"};
		  foobar = {foobar, " 1020"};
		  ozonehl(foo[20], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1021:%s", foobar);
               end
             17'b10_101?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1022"};
		  if (foo[20])
		    begin
		       foobar = {foobar, " 1023"};
		       ozoneacc(foo[18], foobar);
		       foobar = {foobar, " 1024"};
		       foobar = {foobar, " 1025"};
		       if (foo[19])
			 foobar = {foobar, " 1026"};
		       else
			 foobar = {foobar, " 1027"};
		    end
		  else
		    ozonerx(foo, foobar);
		  dude(foobar);
		  $fwrite (fd, " 1028:%s", foobar);
               end
             17'b10_110?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1029"};
		  foobar = {foobar, " 1030"};
		  ozonehl(foo[20], foobar);
		  foobar = {foobar, " 1031"};
		  ozonerx(foo, foobar);
		  dude(foobar);
		  $fwrite (fd, " 1032:%s", foobar);
               end
             17'b10_111?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1033"};
		  foobar = {foobar, " 1034"};
		  ozonehl(foo[20], foobar);
		  foobar = {foobar, " 1035"};
		  ozonerx(foo, foobar);
		  dude(foobar);
		  $fwrite (fd, " 1036:%s", foobar);
               end
             17'b11_001?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1037"};
		  ozonerx(foo, foobar);
		  foobar = {foobar, " 1038"};
		  foobar = {foobar, " 1039"};
		  ozonehl(foo[20], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1040:%s", foobar);
               end
             17'b11_111?_?_????_??_???? :
               begin
		  ozonef1(foo, foobar);
		  foobar = {foobar, " 1041"};
		  foobar = {foobar, " 1042"};
		  ozonerx(foo, foobar);
		  foobar = {foobar, " 1043"};
		  if (foo[20])
		    foobar = {foobar, " 1044"};
		  else
		    foobar = {foobar, " 1045"};
		  dude(foobar);
		  $fwrite (fd, " 1046:%s", foobar);
               end
             17'b00_10??_?_????_?1_1111 :
               casez (foo[11: 5])
		 7'b??_0_010_0:
		   begin
		      foobar = " 1047";
		      ozonecon(foo[14:10], foobar);
		      foobar = {foobar, " 1048"};
		      ozonef1e(foo, foobar);
		      dude(foobar);
		      $fwrite (fd, " 1049:%s", foobar);
		   end
		 7'b00_?_110_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1050"};
		      case ({foo[ 9],foo[ 5]})
			2'b00:
			  begin
			     foobar = {foobar, " 1051"};
			     ozoneae(foo[14:12], foobar);
			     ozonehl(foo[ 5], foobar);
			  end
			2'b01:
			  begin
			     foobar = {foobar, " 1052"};
			     ozoneae(foo[14:12], foobar);
			     ozonehl(foo[ 5], foobar);
			  end
			2'b10:
			  begin
			     foobar = {foobar, " 1053"};
			     ozoneae(foo[14:12], foobar);
			  end
			2'b11: foobar = {foobar, " 1054"};
		      endcase
		      dude(foobar);
		      $fwrite (fd, " 1055:%s", foobar);
		   end
		 7'b01_?_110_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1056"};
		      case ({foo[ 9],foo[ 5]})
			2'b00:
			  begin
			     ozoneae(foo[14:12], foobar);
			     ozonehl(foo[ 5], foobar);
			     foobar = {foobar, " 1057"};
			  end
			2'b01:
			  begin
			     ozoneae(foo[14:12], foobar);
			     ozonehl(foo[ 5], foobar);
			     foobar = {foobar, " 1058"};
			  end
			2'b10:
			  begin
			     ozoneae(foo[14:12], foobar);
			     foobar = {foobar, " 1059"};
			  end
			2'b11: foobar = {foobar, " 1060"};
		      endcase
		      dude(foobar);
		      $fwrite (fd, " 1061:%s", foobar);
		   end
		 7'b10_0_110_0:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1062"};
		      foobar = {foobar, " 1063"};
		      if (foo[12])
			foobar = {foobar, " 1064"};
		      else
			ozonerab({4'b1001, foo[14:12]}, foobar);
		      dude(foobar);
		      $fwrite (fd, " 1065:%s", foobar);
		   end
		 7'b10_0_110_1:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1066"};
		      if (foo[12])
			foobar = {foobar, " 1067"};
		      else
			ozonerab({4'b1001, foo[14:12]}, foobar);
		      foobar = {foobar, " 1068"};
		      dude(foobar);
		      $fwrite (fd, " 1069:%s", foobar);
		   end
		 7'b??_?_000_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1070"};
		      foobar = {foobar, " 1071"};
		      ozonef1e_hl(foo[11:9],foo[ 5],foobar);
		      foobar = {foobar, " 1072"};
		      ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		      dude(foobar);
		      $fwrite (fd, " 1073:%s", foobar);
		   end
		 7'b??_?_100_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1074"};
		      foobar = {foobar, " 1075"};
		      ozonef1e_hl(foo[11:9],foo[ 5],foobar);
		      foobar = {foobar, " 1076"};
		      ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		      dude(foobar);
		      $fwrite (fd, " 1077:%s", foobar);
		   end
		 7'b??_?_001_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1078"};
		      ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		      foobar = {foobar, " 1079"};
		      foobar = {foobar, " 1080"};
		      ozonef1e_hl(foo[11:9],foo[ 5],foobar);
		      dude(foobar);
		      $fwrite (fd, " 1081:%s", foobar);
		   end
		 7'b??_?_011_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1082"};
		      ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		      foobar = {foobar, " 1083"};
		      foobar = {foobar, " 1084"};
		      ozonef1e_hl(foo[11:9],foo[ 5],foobar);
		      dude(foobar);
		      $fwrite (fd, " 1085:%s", foobar);
		   end
		 7'b??_?_101_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1086"};
		      ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		      dude(foobar);
		      $fwrite (fd, " 1087:%s", foobar);
		   end
               endcase
             17'b00_10??_?_????_?0_0110 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1088"};
		  ozoneae(foo[ 8: 6], foobar);
		  ozonef1e_hl(foo[11:9],foo[ 5],foobar);
		  foobar = {foobar, " 1089"};
		  ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		  dude(foobar);
		  $fwrite (fd, " 1090:%s", foobar);
               end
             17'b00_10??_?_????_00_0111 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1091"};
		  if (foo[ 6])
		    foobar = {foobar, " 1092"};
		  else
		    ozonerab({4'b1001, foo[ 8: 6]}, foobar);
		  foobar = {foobar, " 1093"};
		  foobar = {foobar, " 1094"};
		  ozonerme(foo[14:12],foobar);
		  case (foo[11: 9])
		    3'h2,
		      3'h5,
		      3'h6,
		      3'h7:
			ozonef1e_inc_dec(foo[14:9],1'b0,foobar);
		    3'h1,
		      3'h3,
		      3'h4:
			foobar = {foobar, " 1095"};
		  endcase
		  dude(foobar);
		  $fwrite (fd, " 1096:%s", foobar);
               end
             17'b00_10??_?_????_?0_0100 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1097"};
		  ozonef1e_ye(foo[14:9],foo[ 5],foobar);
		  foobar = {foobar, " 1098"};
		  ozoneae(foo[ 8: 6], foobar);
		  ozonef1e_hl(foo[11:9],foo[ 5],foobar);
		  dude(foobar);
		  $fwrite (fd, " 1099:%s", foobar);
               end
             17'b00_10??_?_????_10_0111 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1100"};
		  foobar = {foobar, " 1101"};
		  ozonerme(foo[14:12],foobar);
		  case (foo[11: 9])
		    3'h2,
		      3'h5,
		      3'h6,
		      3'h7:
			ozonef1e_inc_dec(foo[14:9],1'b0,foobar);
		    3'h1,
		      3'h3,
		      3'h4:
			foobar = {foobar, " 1102"};
		  endcase
		  foobar = {foobar, " 1103"};
		  if (foo[ 6])
		    foobar = {foobar, " 1104"};
		  else
		    ozonerab({4'b1001, foo[ 8: 6]}, foobar);
		  dude(foobar);
		  $fwrite (fd, " 1105:%s", foobar);
               end
             17'b00_10??_?_????_?0_1110 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1106"};
		  case (foo[11:9])
		    3'h2:
		      begin
			 foobar = {foobar, " 1107"};
			 if (foo[14:12] == 3'h0)
			   foobar = {foobar, " 1108"};
			 else
			   ozonerme(foo[14:12],foobar);
			 foobar = {foobar, " 1109"};
		      end
		    3'h6:
		      begin
			 foobar = {foobar, " 1110"};
			 if (foo[14:12] == 3'h0)
			   foobar = {foobar, " 1111"};
			 else
			   ozonerme(foo[14:12],foobar);
			 foobar = {foobar, " 1112"};
		      end
		    3'h0:
		      begin
			 foobar = {foobar, " 1113"};
			 if (foo[14:12] == 3'h0)
			   foobar = {foobar, " 1114"};
			 else
			   ozonerme(foo[14:12],foobar);
			 foobar = {foobar, " 1115"};
			 if (foo[ 7: 5] >= 3'h5)
			   foobar = {foobar, " 1116"};
			 else
			   ozonexe(foo[ 8: 5], foobar);
		      end
		    3'h1:
		      begin
			 foobar = {foobar, " 1117"};
			 if (foo[14:12] == 3'h0)
			   foobar = {foobar, " 1118"};
			 else
			   ozonerme(foo[14:12],foobar);
			 foobar = {foobar, " 1119"};
			 if (foo[ 7: 5] >= 3'h5)
			   foobar = {foobar, " 1120"};
			 else
			   ozonexe(foo[ 8: 5], foobar);
		      end
		    3'h4:
		      begin
			 foobar = {foobar, " 1121"};
			 if (foo[14:12] == 3'h0)
			   foobar = {foobar, " 1122"};
			 else
			   ozonerme(foo[14:12],foobar);
			 foobar = {foobar, " 1123"};
			 if (foo[ 7: 5] >= 3'h5)
			   foobar = {foobar, " 1124"};
			 else
			   ozonexe(foo[ 8: 5], foobar);
		      end
		    3'h5:
		      begin
			 foobar = {foobar, " 1125"};
			 if (foo[14:12] == 3'h0)
			   foobar = {foobar, " 1126"};
			 else
			   ozonerme(foo[14:12],foobar);
			 foobar = {foobar, " 1127"};
			 if (foo[ 7: 5] >= 3'h5)
			   foobar = {foobar, " 1128"};
			 else
			   ozonexe(foo[ 8: 5], foobar);
		      end
		  endcase
		  dude(foobar);
		  $fwrite (fd, " 1129:%s", foobar);
               end
             17'b00_10??_?_????_?0_1111 :
               casez (foo[14: 9])
		 6'b001_10_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1130"};
		      foobar = {foobar, " 1131"};
		      ozonef1e_hl(foo[ 7: 5],foo[ 9],foobar);
		      foobar = {foobar, " 1132"};
		      ozonexe(foo[ 8: 5], foobar);
		      dude(foobar);
		      $fwrite (fd, " 1133:%s", foobar);
		   end
		 6'b???_11_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1134"};
		      ozoneae(foo[14:12], foobar);
		      ozonef1e_hl(foo[ 7: 5],foo[ 9],foobar);
		      foobar = {foobar, " 1135"};
		      ozonexe(foo[ 8: 5], foobar);
		      dude(foobar);
		      $fwrite (fd, " 1136:%s", foobar);
		   end
		 6'b000_10_1,
		   6'b010_10_1,
		   6'b100_10_1,
		   6'b110_10_1:
		     begin
			ozonef1e(foo, foobar);
			foobar = {foobar, " 1137"};
			ozonerab({4'b1001, foo[14:12]}, foobar);
			foobar = {foobar, " 1138"};
			if ((foo[ 7: 5] >= 3'h1) & (foo[ 7: 5] <= 3'h3))
			  foobar = {foobar, " 1139"};
			else
			  ozonexe(foo[ 8: 5], foobar);
			dude(foobar);
			$fwrite (fd, " 1140:%s", foobar);
		     end
		 6'b000_10_0,
		   6'b010_10_0,
		   6'b100_10_0,
		   6'b110_10_0:
		     begin
			ozonef1e(foo, foobar);
			foobar = {foobar, " 1141"};
			foobar = {foobar, " 1142"};
			ozonerab({4'b1001, foo[14:12]}, foobar);
			foobar = {foobar, " 1143"};
			foobar = {foobar, " 1144"};
			ozonef1e_h(foo[ 7: 5],foobar);
			foobar = {foobar, " 1145"};
			ozonexe(foo[ 8: 5], foobar);
			dude(foobar);
			$fwrite (fd, " 1146:%s", foobar);
		     end
		 6'b???_00_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1147"};
		      if (foo[ 9])
			begin
			   foobar = {foobar, " 1148"};
			   ozoneae(foo[14:12], foobar);
			end
		      else
			begin
			   foobar = {foobar, " 1149"};
			   ozoneae(foo[14:12], foobar);
			   foobar = {foobar, " 1150"};
			end
		      foobar = {foobar, " 1151"};
		      foobar = {foobar, " 1152"};
		      ozonef1e_h(foo[ 7: 5],foobar);
		      foobar = {foobar, " 1153"};
		      ozonexe(foo[ 8: 5], foobar);
		      dude(foobar);
		      $fwrite (fd, " 1154:%s", foobar);
		   end
		 6'b???_01_?:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1155"};
		      ozoneae(foo[14:12], foobar);
		      if (foo[ 9])
			foobar = {foobar, " 1156"};
		      else
			foobar = {foobar, " 1157"};
		      foobar = {foobar, " 1158"};
		      foobar = {foobar, " 1159"};
		      ozonef1e_h(foo[ 7: 5],foobar);
		      foobar = {foobar, " 1160"};
		      ozonexe(foo[ 8: 5], foobar);
		      dude(foobar);
		      $fwrite (fd, " 1161:%s", foobar);
		   end
		 6'b011_10_0:
		   begin
		      ozonef1e(foo, foobar);
		      foobar = {foobar, " 1162"};
		      case (foo[ 8: 5])
			4'h0:  foobar = {foobar, " 1163"};
			4'h1:  foobar = {foobar, " 1164"};
			4'h2:  foobar = {foobar, " 1165"};
			4'h3:  foobar = {foobar, " 1166"};
			4'h4:  foobar = {foobar, " 1167"};
			4'h5:  foobar = {foobar, " 1168"};
			4'h8:  foobar = {foobar, " 1169"};
			4'h9:  foobar = {foobar, " 1170"};
			4'ha:  foobar = {foobar, " 1171"};
			4'hb:  foobar = {foobar, " 1172"};
			4'hc:  foobar = {foobar, " 1173"};
			4'hd:  foobar = {foobar, " 1174"};
			default: foobar = {foobar, " 1175"};
		      endcase
		      dude(foobar);
		      $fwrite (fd, " 1176:%s", foobar);
		   end
		 default: foobar = {foobar, " 1177"};
               endcase
             17'b00_10??_?_????_?0_110? :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1178"};
		  foobar = {foobar, " 1179"};
		  ozonef1e_hl(foo[11:9], foo[0], foobar);
		  foobar = {foobar, " 1180"};
		  ozonef1e_ye(foo[14:9],1'b0,foobar);
		  foobar = {foobar, " 1181"};
		  ozonef1e_h(foo[ 7: 5],foobar);
		  foobar = {foobar, " 1182"};
		  ozonexe(foo[ 8: 5], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1183:%s", foobar);
               end
             17'b00_10??_?_????_?1_110? :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1184"};
		  foobar = {foobar, " 1185"};
		  ozonef1e_hl(foo[11:9],foo[0],foobar);
		  foobar = {foobar, " 1186"};
		  ozonef1e_ye(foo[14:9],foo[ 0],foobar);
		  foobar = {foobar, " 1187"};
		  foobar = {foobar, " 1188"};
		  ozonef1e_h(foo[ 7: 5],foobar);
		  foobar = {foobar, " 1189"};
		  ozonexe(foo[ 8: 5], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1190:%s", foobar);
               end
             17'b00_10??_?_????_?0_101? :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1191"};
		  ozonef1e_ye(foo[14:9],foo[ 0],foobar);
		  foobar = {foobar, " 1192"};
		  foobar = {foobar, " 1193"};
		  ozonef1e_hl(foo[11:9],foo[0],foobar);
		  foobar = {foobar, " 1194"};
		  foobar = {foobar, " 1195"};
		  ozonef1e_h(foo[ 7: 5],foobar);
		  foobar = {foobar, " 1196"};
		  ozonexe(foo[ 8: 5], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1197:%s", foobar);
               end
             17'b00_10??_?_????_?0_1001 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1198"};
		  foobar = {foobar, " 1199"};
		  ozonef1e_h(foo[11:9],foobar);
		  foobar = {foobar, " 1200"};
		  ozonef1e_ye(foo[14:9],1'b0,foobar);
		  foobar = {foobar, " 1201"};
		  case (foo[ 7: 5])
		    3'h1,
		      3'h2,
		      3'h3:
			foobar = {foobar, " 1202"};
		    default:
		      begin
			 foobar = {foobar, " 1203"};
			 foobar = {foobar, " 1204"};
			 ozonexe(foo[ 8: 5], foobar);
		      end
		  endcase
		  dude(foobar);
		  $fwrite (fd, " 1205:%s", foobar);
               end
             17'b00_10??_?_????_?0_0101 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1206"};
		  case (foo[11: 9])
		    3'h1,
		      3'h3,
		      3'h4:
			foobar = {foobar, " 1207"};
		    default:
		      begin
			 ozonef1e_ye(foo[14:9],1'b0,foobar);
			 foobar = {foobar, " 1208"};
			 foobar = {foobar, " 1209"};
		      end
		  endcase
		  foobar = {foobar, " 1210"};
		  foobar = {foobar, " 1211"};
		  ozonef1e_h(foo[ 7: 5],foobar);
		  foobar = {foobar, " 1212"};
		  ozonexe(foo[ 8: 5], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1213:%s", foobar);
               end
             17'b00_10??_?_????_?1_1110 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1214"};
		  ozonef1e_ye(foo[14:9],1'b0,foobar);
		  foobar = {foobar, " 1215"};
		  foobar = {foobar, " 1216"};
		  ozonef1e_h(foo[11: 9],foobar);
		  foobar = {foobar, " 1217"};
		  foobar = {foobar, " 1218"};
		  ozonef1e_h(foo[ 7: 5],foobar);
		  foobar = {foobar, " 1219"};
		  ozonexe(foo[ 8: 5], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1220:%s", foobar);
               end
             17'b00_10??_?_????_?0_1000 :
               begin
		  ozonef1e(foo, foobar);
		  foobar = {foobar, " 1221"};
		  ozonef1e_ye(foo[14:9],1'b0,foobar);
		  foobar = {foobar, " 1222"};
		  foobar = {foobar, " 1223"};
		  ozonef1e_h(foo[11: 9],foobar);
		  foobar = {foobar, " 1224"};
		  foobar = {foobar, " 1225"};
		  ozonef1e_h(foo[ 7: 5],foobar);
		  foobar = {foobar, " 1226"};
		  ozonexe(foo[ 8: 5], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1227:%s", foobar);
               end
             17'b10_01??_?_????_??_???? :
               begin
		  if (foo[27])
		    foobar = " 1228";
		  else
		    foobar = " 1229";
		  ozonecon(foo[20:16], foobar);
		  foobar = {foobar, " 1230"};
		  ozonef2(foo[31:0], foobar);
		  dude(foobar);
		  $fwrite (fd, " 1231:%s", foobar);
               end
             17'b00_1000_?_????_01_0011 :
               if (~|foo[ 9: 8])
		 begin
		    if (foo[ 7])
		      foobar = " 1232";
		    else
		      foobar = " 1233";
		    ozonecon(foo[14:10], foobar);
		    foobar = {foobar, " 1234"};
		    ozonef2e(foo[31:0], foobar);
		    dude(foobar);
		    $fwrite (fd, " 1235:%s", foobar);
		 end
               else
		 begin
		    foobar = " 1236";
		    ozonecon(foo[14:10], foobar);
		    foobar = {foobar, " 1237"};
		    ozonef3e(foo[31:0], foobar);
		    dude(foobar);
		    $fwrite (fd, " 1238:%s", foobar);
		 end
             17'b11_110?_1_????_??_???? :
               begin
		  ozonef3(foo[31:0], foobar);
		  dude(foobar);
		  $fwrite(fd, " 1239:%s", foobar);
               end
             17'b11_110?_0_????_??_???? :
               begin : f4_body
		  casez (foo[24:20])
		    5'b0_1110,
		      5'b1_0???,
		      5'b1_1111:
			begin
			   $fwrite (fd, " 1240");
			end
		    5'b0_00??:
		      begin
			 ozoneacc(foo[26], foobar);
			 foobar = {foobar, " 1241"};
			 ozoneacc(foo[25], foobar);
			 ozonebmuop(foo[24:20], foobar);
			 ozoneae(foo[18:16], foobar);
			 foobar = {foobar, " 1242"};
			 dude(foobar);
			 $fwrite(fd, " 1243:%s", foobar);
		      end
		    5'b0_01??:
		      begin
			 ozoneacc(foo[26], foobar);
			 foobar = {foobar, " 1244"};
			 ozoneacc(foo[25], foobar);
			 ozonebmuop(foo[24:20], foobar);
			 ozonearm(foo[18:16], foobar);
			 dude(foobar);
			 $fwrite(fd, " 1245:%s", foobar);
		      end
		    5'b0_1011:
		      begin
			 ozoneacc(foo[26], foobar);
			 foobar = {foobar, " 1246"};
			 ozonebmuop(foo[24:20], foobar);
			 foobar = {foobar, " 1247"};
			 ozoneae(foo[18:16], foobar);
			 foobar = {foobar, " 1248"};
			 dude(foobar);
			 $fwrite(fd, " 1249:%s", foobar);
		      end
		    5'b0_100?,
		      5'b0_1010,
		      5'b0_110? :
			begin
			   ozoneacc(foo[26], foobar);
			   foobar = {foobar, " 1250"};
			   ozonebmuop(foo[24:20], foobar);
			   foobar = {foobar, " 1251"};
			   ozoneacc(foo[25], foobar);
			   foobar = {foobar, " 1252"};
			   ozoneae(foo[18:16], foobar);
			   foobar = {foobar, " 1253"};
			   dude(foobar);
			   $fwrite(fd, " 1254:%s", foobar);
			end
		    5'b0_1111 :
		      begin
			 ozoneacc(foo[26], foobar);
			 foobar = {foobar, " 1255"};
			 ozoneacc(foo[25], foobar);
			 foobar = {foobar, " 1256"};
			 ozoneae(foo[18:16], foobar);
			 dude(foobar);
			 $fwrite(fd, " 1257:%s", foobar);
		      end
		    5'b1_10??,
		      5'b1_110?,
		      5'b1_1110 :
			begin
			   ozoneacc(foo[26], foobar);
			   foobar = {foobar, " 1258"};
			   ozonebmuop(foo[24:20], foobar);
			   foobar = {foobar, " 1259"};
			   ozoneacc(foo[25], foobar);
			   foobar = {foobar, " 1260"};
			   ozonearm(foo[18:16], foobar);
			   foobar = {foobar, " 1261"};
			   dude(foobar);
			   $fwrite(fd, " 1262:%s", foobar);
			end
		  endcase
               end
             17'b11_100?_?_????_??_???? :
               casez (foo[23:19])
		 5'b111??,
		   5'b0111?:
		     begin
			ozoneae(foo[26:24], foobar);
			foobar = {foobar, " 1263"};
			ozonef3f4imop(foo[23:19], foobar);
			foobar = {foobar, " 1264"};
			ozoneae(foo[18:16], foobar);
			foobar = {foobar, " 1265"};
			skyway(foo[15:12], foobar);
			skyway(foo[11: 8], foobar);
			skyway(foo[ 7: 4], foobar);
			skyway(foo[ 3:0], foobar);
			foobar = {foobar, " 1266"};
			dude(foobar);
			$fwrite(fd, " 1267:%s", foobar);
		     end
		 5'b?0???,
		   5'b110??:
		     begin
			ozoneae(foo[26:24], foobar);
			foobar = {foobar, " 1268"};
			if (foo[23:21] == 3'b100)
			  foobar = {foobar, " 1269"};
			ozoneae(foo[18:16], foobar);
			if (foo[19])
			  foobar = {foobar, " 1270"};
			else
			  foobar = {foobar, " 1271"};
			ozonef3f4imop(foo[23:19], foobar);
			foobar = {foobar, " 1272"};
			ozonef3f4_iext(foo[20:19], foo[15:0], foobar);
			dude(foobar);
			$fwrite(fd, " 1273:%s", foobar);
		     end
		 5'b010??,
		   5'b0110?:
		     begin
			ozoneae(foo[18:16], foobar);
			if (foo[19])
			  foobar = {foobar, " 1274"};
			else
			  foobar = {foobar, " 1275"};
			ozonef3f4imop(foo[23:19], foobar);
			foobar = {foobar, " 1276"};
			ozonef3f4_iext(foo[20:19], foo[15:0], foobar);
			dude(foobar);
			$fwrite(fd, " 1277:%s", foobar);
		     end
               endcase
             17'b00_1000_?_????_11_0011 :
               begin
		  foobar = " 1278";
		  ozonecon(foo[14:10], foobar);
		  foobar = {foobar, " 1279"};
		  casez (foo[25:21])
		    5'b0_1110,
		      5'b1_0???,
		      5'b1_1111:
			begin
			   $fwrite(fd, " 1280");
			end
		    5'b0_00??:
		      begin
			 ozoneae(foo[20:18], foobar);
			 foobar = {foobar, " 1281"};
			 ozoneae(foo[17:15], foobar);
			 ozonebmuop(foo[25:21], foobar);
			 ozoneae(foo[ 8: 6], foobar);
			 foobar = {foobar, " 1282"};
			 dude(foobar);
			 $fwrite(fd, " 1283:%s", foobar);
		      end
		    5'b0_01??:
		      begin
			 ozoneae(foo[20:18], foobar);
			 foobar = {foobar, " 1284"};
			 ozoneae(foo[17:15], foobar);
			 ozonebmuop(foo[25:21], foobar);
			 ozonearm(foo[ 8: 6], foobar);
			 dude(foobar);
			 $fwrite(fd, " 1285:%s", foobar);
		      end
		    5'b0_1011:
		      begin
			 ozoneae(foo[20:18], foobar);
			 foobar = {foobar, " 1286"};
			 ozonebmuop(foo[25:21], foobar);
			 foobar = {foobar, " 1287"};
			 ozoneae(foo[ 8: 6], foobar);
			 foobar = {foobar, " 1288"};
			 dude(foobar);
			 $fwrite(fd, " 1289:%s", foobar);
		      end
		    5'b0_100?,
		      5'b0_1010,
		      5'b0_110? :
			begin
			   ozoneae(foo[20:18], foobar);
			   foobar = {foobar, " 1290"};
			   ozonebmuop(foo[25:21], foobar);
			   foobar = {foobar, " 1291"};
			   ozoneae(foo[17:15], foobar);
			   foobar = {foobar, " 1292"};
			   ozoneae(foo[ 8: 6], foobar);
			   foobar = {foobar, " 1293"};
			   dude(foobar);
			   $fwrite(fd, " 1294:%s", foobar);
			end
		    5'b0_1111 :
		      begin
			 ozoneae(foo[20:18], foobar);
			 foobar = {foobar, " 1295"};
			 ozoneae(foo[17:15], foobar);
			 foobar = {foobar, " 1296"};
			 ozoneae(foo[ 8: 6], foobar);
			 dude(foobar);
			 $fwrite(fd, " 1297:%s", foobar);
		      end
		    5'b1_10??,
		      5'b1_110?,
		      5'b1_1110 :
			begin
			   ozoneae(foo[20:18], foobar);
			   foobar = {foobar, " 1298"};
			   ozonebmuop(foo[25:21], foobar);
			   foobar = {foobar, " 1299"};
			   ozoneae(foo[17:15], foobar);
			   foobar = {foobar, " 1300"};
			   ozonearm(foo[ 8: 6], foobar);
			   foobar = {foobar, " 1301"};
			   dude(foobar);
			   $fwrite(fd, " 1302:%s", foobar);
			end
		  endcase
               end
             17'b00_0010_?_????_??_???? :
               begin
		  $fwrite(fd, " 1304a:%x;%x", foobar, foo[25:20]);
		  ozonerab({1'b0, foo[25:20]}, foobar);
		  $fwrite(fd, " 1304b:%x", foobar);
		  foobar = {foobar, " 1303"};
		  $fwrite(fd, " 1304c:%x;%x", foobar, foo[19:16]);
		  skyway(foo[19:16], foobar);
		  $fwrite(fd, " 1304d:%x", foobar);
		  dude(foobar);
		  $fwrite(fd, " 1304e:%x", foobar);
		  $fwrite(fd, " 1304:%s", foobar);
               end
             17'b00_01??_?_????_??_???? :
               begin
		  if (foo[27])
		    begin
		       foobar = {foobar, " 1305"};
		       if (foo[26])
			 foobar = {foobar, " 1306"};
		       else
			 foobar = {foobar, " 1307"};
		       skyway(foo[19:16], foobar);
		       foobar = {foobar, " 1308"};
		       ozonerab({1'b0, foo[25:20]}, foobar);
		    end
		  else
		    begin
		       ozonerab({1'b0, foo[25:20]}, foobar);
		       foobar = {foobar, " 1309"};
		       if (foo[26])
			 foobar = {foobar, " 1310"};
		       else
			 foobar = {foobar, " 1311"};
		       skyway(foo[19:16], foobar);
		       foobar = {foobar, " 1312"};
		    end
		  dude(foobar);
		  $fwrite(fd, " 1313:%s", foobar);
               end
             17'b01_000?_?_????_??_???? :
               begin
		  if (foo[26])
		    begin
		       ozonerb(foo[25:20], foobar);
		       foobar = {foobar, " 1314"};
		       ozoneae(foo[18:16], foobar);
		       ozonehl(foo[19], foobar);
		    end
		  else
		    begin
		       ozoneae(foo[18:16], foobar);
		       ozonehl(foo[19], foobar);
		       foobar = {foobar, " 1315"};
		       ozonerb(foo[25:20], foobar);
		    end
		  dude(foobar);
		  $fwrite(fd, " 1316:%s", foobar);
               end
             17'b01_10??_?_????_??_???? :
               begin
		  if (foo[27])
		    begin
		       ozonerab({1'b0, foo[25:20]}, foobar);
		       foobar = {foobar, " 1317"};
		       ozonerx(foo, foobar);
		    end
		  else
		    begin
		       ozonerx(foo, foobar);
		       foobar = {foobar, " 1318"};
		       ozonerab({1'b0, foo[25:20]}, foobar);
		    end
		  dude(foobar);
		  $fwrite(fd, " 1319:%s", foobar);
               end
             17'b11_101?_?_????_??_???? :
               begin
		  ozonerab (foo[26:20], foobar);
		  foobar = {foobar, " 1320"};
		  skyway(foo[19:16], foobar);
		  skyway(foo[15:12], foobar);
		  skyway(foo[11: 8], foobar);
		  skyway(foo[ 7: 4], foobar);
		  skyway(foo[ 3: 0], foobar);
		  dude(foobar);
		  $fwrite(fd, " 1321:%s", foobar);
               end
             17'b11_0000_?_????_??_???? :
               begin
		  casez (foo[25:23])
		    3'b00?:
		      begin
			 ozonerab(foo[22:16], foobar);
			 foobar = {foobar, " 1322"};
		      end
		    3'b01?:
		      begin
			 foobar = {foobar, " 1323"};
			 if (foo[22:16]>=7'h60)
			   foobar = {foobar, " 1324"};
			 else
			   ozonerab(foo[22:16], foobar);
		      end
		    3'b110:
		      foobar = {foobar, " 1325"};
		    3'b10?:
		      begin
			 foobar = {foobar, " 1326"};
			 if (foo[22:16]>=7'h60)
			   foobar = {foobar, " 1327"};
			 else
			   ozonerab(foo[22:16], foobar);
		      end
		    3'b111:
		      begin
			 foobar = {foobar, " 1328"};
			 ozonerab(foo[22:16], foobar);
			 foobar = {foobar, " 1329"};
		      end
		  endcase
		  dude(foobar);
		  $fwrite(fd, " 1330:%s", foobar);
               end
             17'b00_10??_?_????_?1_0000 :
               begin
		  if (foo[27])
		    begin
		       foobar = {foobar, " 1331"};
		       ozonerp(foo[14:12], foobar);
		       foobar = {foobar, " 1332"};
		       skyway(foo[19:16], foobar);
		       skyway({foo[15],foo[11: 9]}, foobar);
		       skyway(foo[ 8: 5], foobar);
		       foobar = {foobar, " 1333"};
		       if (foo[26:20]>=7'h60)
			 foobar = {foobar, " 1334"};
		       else
			 ozonerab(foo[26:20], foobar);
		    end
		  else
		    begin
		       ozonerab(foo[26:20], foobar);
		       foobar = {foobar, " 1335"};
		       foobar = {foobar, " 1336"};
		       ozonerp(foo[14:12], foobar);
		       foobar = {foobar, " 1337"};
		       skyway(foo[19:16], foobar);
		       skyway({foo[15],foo[11: 9]}, foobar);
		       skyway(foo[ 8: 5], foobar);
		       foobar = {foobar, " 1338"};
		    end
		  dude(foobar);
		  $fwrite(fd, " 1339:%s", foobar);
               end
             17'b00_101?_1_0000_?1_0010 :
               if (~|foo[11: 7])
		 begin
		    if (foo[ 6])
		      begin
			 foobar = {foobar, " 1340"};
			 ozonerp(foo[14:12], foobar);
			 foobar = {foobar, " 1341"};
			 ozonejk(foo[ 5], foobar);
			 foobar = {foobar, " 1342"};
			 if (foo[26:20]>=7'h60)
			   foobar = {foobar, " 1343"};
			 else
			   ozonerab(foo[26:20], foobar);
		      end
		    else
		      begin
			 ozonerab(foo[26:20], foobar);
			 foobar = {foobar, " 1344"};
			 foobar = {foobar, " 1345"};
			 ozonerp(foo[14:12], foobar);
			 foobar = {foobar, " 1346"};
			 ozonejk(foo[ 5], foobar);
			 foobar = {foobar, " 1347"};
		      end
		    dude(foobar);
		    $fwrite(fd, " 1348:%s", foobar);
		 end
               else
		 $fwrite(fd, " 1349");
             17'b00_100?_0_0011_?1_0101 :
               if (~|foo[ 8: 7])
		 begin
		    if (foo[6])
		      begin
			 ozonerab(foo[26:20], foobar);
			 foobar = {foobar, " 1350"};
			 ozoneye(foo[14: 9],foo[ 5], foobar);
		      end
		    else
		      begin
			 ozoneye(foo[14: 9],foo[ 5], foobar);
			 foobar = {foobar, " 1351"};
			 if (foo[26:20]>=7'h60)
			   foobar = {foobar, " 1352"};
			 else
			   ozonerab(foo[26:20], foobar);
		      end
		    dude(foobar);
		    $fwrite(fd, " 1353:%s", foobar);
		 end
               else
		 $fwrite(fd, " 1354");
             17'b00_1001_0_0000_?1_0010 :
               if (~|foo[25:20])
		 begin
		    ozoneye(foo[14: 9],1'b0, foobar);
		    foobar = {foobar, " 1355"};
		    ozonef1e_h(foo[11: 9],foobar);
		    foobar = {foobar, " 1356"};
		    ozonef1e_h(foo[ 7: 5],foobar);
		    foobar = {foobar, " 1357"};
		    ozonexe(foo[ 8: 5], foobar);
		    dude(foobar);
		    $fwrite(fd, " 1358:%s", foobar);
		 end
               else
		 $fwrite(fd, " 1359");
             17'b00_101?_0_????_?1_0010 :
               if (~foo[13])
		 begin
		    if (foo[12])
		      begin
			 foobar = {foobar, " 1360"};
			 if (foo[26:20]>=7'h60)
			   foobar = {foobar, " 1361"};
			 else
			   ozonerab(foo[26:20], foobar);
			 foobar = {foobar, " 1362"};
			 foobar = {foobar, " 1363"};
			 skyway({1'b0,foo[18:16]}, foobar);
			 skyway({foo[15],foo[11: 9]}, foobar);
			 skyway(foo[ 8: 5], foobar);
			 dude(foobar);
			 $fwrite(fd, " 1364:%s", foobar);
		      end
		    else
		      begin
			 ozonerab(foo[26:20], foobar);
			 foobar = {foobar, " 1365"};
			 foobar = {foobar, " 1366"};
			 skyway({1'b0,foo[18:16]}, foobar);
			 skyway({foo[15],foo[11: 9]}, foobar);
			 skyway(foo[ 8: 5], foobar);
			 dude(foobar);
			 $fwrite(fd, " 1367:%s", foobar);
		      end
		 end
               else
		 $fwrite(fd, " 1368");
             17'b01_01??_?_????_??_???? :
               begin
		  ozonerab({1'b0,foo[27:26],foo[19:16]}, foobar);
		  foobar = {foobar, " 1369"};
		  ozonerab({1'b0,foo[25:20]}, foobar);
		  dude(foobar);
		  $fwrite(fd, " 1370:%s", foobar);
               end
             17'b00_100?_?_???0_11_0101 :
               if (~foo[6])
		 begin
		    foobar = " 1371";
		    ozonecon(foo[14:10], foobar);
		    foobar = {foobar, " 1372"};
		    ozonerab({foo[ 9: 7],foo[19:16]}, foobar);
		    foobar = {foobar, " 1373"};
		    ozonerab({foo[26:20]}, foobar);
		    dude(foobar);
		    $fwrite(fd, " 1374:%s", foobar);
		 end
               else
		 $fwrite(fd, " 1375");
             17'b00_1000_?_????_?1_0010 :
               if (~|foo[25:24])
		 begin
		    ozonery(foo[23:20], foobar);
		    foobar = {foobar, " 1376"};
		    ozonerp(foo[14:12], foobar);
		    foobar = {foobar, " 1377"};
		    skyway(foo[19:16], foobar);
		    skyway({foo[15],foo[11: 9]}, foobar);
		    skyway(foo[ 8: 5], foobar);
		    dude(foobar);
		    $fwrite(fd, " 1378:%s", foobar);
		 end
               else if ((foo[25:24] == 2'b10) & ~|foo[19:15] & ~|foo[11: 6])
		 begin
		    ozonery(foo[23:20], foobar);
		    foobar = {foobar, " 1379"};
		    ozonerp(foo[14:12], foobar);
		    foobar = {foobar, " 1380"};
		    ozonejk(foo[ 5], foobar);
		    dude(foobar);
		    $fwrite(fd, " 1381:%s", foobar);
		 end
               else
		 $fwrite(fd, " 1382");
             17'b11_01??_?_????_??_????,
               17'b10_00??_?_????_??_???? :
		 if (foo[30])
		   $fwrite(fd, " 1383:%s", foo[27:16]);
		 else
		   $fwrite(fd, " 1384:%s", foo[27:16]);
             17'b00_10??_?_????_01_1000 :
               if (~foo[6])
		 begin
		    if (foo[7])
		      $fwrite(fd, " 1385:%s", foo[27: 8]);
		    else
		      $fwrite(fd, " 1386:%s", foo[27: 8]);
		 end
               else
		 $fwrite(fd, " 1387");
             17'b00_10??_?_????_11_1000 :
               begin
		  foobar = " 1388";
		  ozonecon(foo[14:10], foobar);
		  foobar = {foobar, " 1389"};
		  if (foo[15])
		    foobar = {foobar, " 1390"};
		  else
		    foobar = {foobar, " 1391"};
		  skyway(foo[27:24], foobar);
		  skyway(foo[23:20], foobar);
		  skyway(foo[19:16], foobar);
		  skyway(foo[ 9: 6], foobar);
		  dude(foobar);
		  $fwrite(fd, " 1392:%s", foobar);
               end
             17'b11_0001_?_????_??_???? :
               casez (foo[25:22])
		 4'b01?? :
		   begin
		      foobar = " 1393";
		      ozonecon(foo[20:16], foobar);
		      case (foo[23:21])
			3'h0 :  foobar = {foobar, " 1394"};
			3'h1 :  foobar = {foobar, " 1395"};
			3'h2 :  foobar = {foobar, " 1396"};
			3'h3 :  foobar = {foobar, " 1397"};
			3'h4 :  foobar = {foobar, " 1398"};
			3'h5 :  foobar = {foobar, " 1399"};
			3'h6 :  foobar = {foobar, " 1400"};
			3'h7 :  foobar = {foobar, " 1401"};
		      endcase
		      dude(foobar);
		      $fwrite(fd, " 1402:%s", foobar);
		   end
		 4'b0000 :
		   $fwrite(fd, " 1403:%s", foo[21:16]);
		 4'b0010 :
		   if (~|foo[21:16])
                     $fwrite(fd, " 1404");
		 4'b1010 :
		   if (~|foo[21:17])
		     begin
			if (foo[16])
			  $fwrite(fd, " 1405");
			else
			  $fwrite(fd, " 1406");
		     end
		 default :
		   $fwrite(fd, " 1407");
               endcase
             17'b01_11??_?_????_??_???? :
               if (foo[27:23] === 5'h00)
		 $fwrite(fd, " 1408:%s", foo[22:16]);
               else
		 $fwrite(fd, " 1409:%s", foo[22:16]);
             default: $fwrite(fd, " 1410");
	   endcase
      end
   endtask

   //(query-replace-regexp "\\([a-z0-9_]+\\) *( *\\([][a-z0-9_~': ]+\\) *, *\\([][a-z0-9'~: ]+\\) *, *\\([][a-z0-9'~: ]+\\) *);" "$c(\"\\1(\",\\2,\",\",\\3,\",\",\\4,\");\");" nil nil nil)
   //(query-replace-regexp "\\([a-z0-9_]+\\) *( *\\([][a-z0-9_~': ]+\\) *, *\\([][a-z0-9'~: ]+\\) *);" "$c(\"\\1(\",\\2,\",\",\\3,\");\");" nil nil nil)

endmodule
