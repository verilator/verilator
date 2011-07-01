// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

`include "verilated.v"

module t_case_write2_tasks ();

   // verilator lint_off WIDTH
   // verilator lint_off CASEINCOMPLETE

 `define FD_BITS 31:0

   parameter STRLEN = 78;
   task ozonerab;
      input [6:0] rab;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (rab[6:0])
	   7'h00 : $fwrite (fd, " 0");
	   7'h01 : $fwrite (fd, " 1");
	   7'h02 : $fwrite (fd, " 2");
	   7'h03 : $fwrite (fd, " 3");
	   7'h04 : $fwrite (fd, " 4");
	   7'h05 : $fwrite (fd, " 5");
	   7'h06 : $fwrite (fd, " 6");
	   7'h07 : $fwrite (fd, " 7");
	   7'h08 : $fwrite (fd, " 8");
	   7'h09 : $fwrite (fd, " 9");
	   7'h0a : $fwrite (fd, " 10");
	   7'h0b : $fwrite (fd, " 11");
	   7'h0c : $fwrite (fd, " 12");
	   7'h0d : $fwrite (fd, " 13");
	   7'h0e : $fwrite (fd, " 14");
	   7'h0f : $fwrite (fd, " 15");
	   7'h10 : $fwrite (fd, " 16");
	   7'h11 : $fwrite (fd, " 17");
	   7'h12 : $fwrite (fd, " 18");
	   7'h13 : $fwrite (fd, " 19");
	   7'h14 : $fwrite (fd, " 20");
	   7'h15 : $fwrite (fd, " 21");
	   7'h16 : $fwrite (fd, " 22");
	   7'h17 : $fwrite (fd, " 23");
	   7'h18 : $fwrite (fd, " 24");
	   7'h19 : $fwrite (fd, " 25");
	   7'h1a : $fwrite (fd, " 26");
	   7'h1b : $fwrite (fd, " 27");
	   7'h1c : $fwrite (fd, " 28");
	   7'h1d : $fwrite (fd, " 29");
	   7'h1e : $fwrite (fd, " 30");
	   7'h1f : $fwrite (fd, " 31");
	   7'h20 : $fwrite (fd, " 32");
	   7'h21 : $fwrite (fd, " 33");
	   7'h22 : $fwrite (fd, " 34");
	   7'h23 : $fwrite (fd, " 35");
	   7'h24 : $fwrite (fd, " 36");
	   7'h25 : $fwrite (fd, " 37");
	   7'h26 : $fwrite (fd, " 38");
	   7'h27 : $fwrite (fd, " 39");
	   7'h28 : $fwrite (fd, " 40");
	   7'h29 : $fwrite (fd, " 41");
	   7'h2a : $fwrite (fd, " 42");
	   7'h2b : $fwrite (fd, " 43");
	   7'h2c : $fwrite (fd, " 44");
	   7'h2d : $fwrite (fd, " 45");
	   7'h2e : $fwrite (fd, " 46");
	   7'h2f : $fwrite (fd, " 47");
	   7'h30 : $fwrite (fd, " 48");
	   7'h31 : $fwrite (fd, " 49");
	   7'h32 : $fwrite (fd, " 50");
	   7'h33 : $fwrite (fd, " 51");
	   7'h34 : $fwrite (fd, " 52");
	   7'h35 : $fwrite (fd, " 53");
	   7'h36 : $fwrite (fd, " 54");
	   7'h37 : $fwrite (fd, " 55");
	   7'h38 : $fwrite (fd, " 56");
	   7'h39 : $fwrite (fd, " 57");
	   7'h3a : $fwrite (fd, " 58");
	   7'h3b : $fwrite (fd, " 59");
	   7'h3c : $fwrite (fd, " 60");
	   7'h3d : $fwrite (fd, " 61");
	   7'h3e : $fwrite (fd, " 62");
	   7'h3f : $fwrite (fd, " 63");
	   7'h40 : $fwrite (fd, " 64");
	   7'h41 : $fwrite (fd, " 65");
	   7'h42 : $fwrite (fd, " 66");
	   7'h43 : $fwrite (fd, " 67");
	   7'h44 : $fwrite (fd, " 68");
	   7'h45 : $fwrite (fd, " 69");
	   7'h46 : $fwrite (fd, " 70");
	   7'h47 : $fwrite (fd, " 71");
	   7'h48 : $fwrite (fd, " 72");
	   7'h49 : $fwrite (fd, " 73");
	   7'h4a : $fwrite (fd, " 74");
	   7'h4b : $fwrite (fd, " 75");
	   7'h4c : $fwrite (fd, " 76");
	   7'h4d : $fwrite (fd, " 77");
	   7'h4e : $fwrite (fd, " 78");
	   7'h4f : $fwrite (fd, " 79");
	   7'h50 : $fwrite (fd, " 80");
	   7'h51 : $fwrite (fd, " 81");
	   7'h52 : $fwrite (fd, " 82");
	   7'h53 : $fwrite (fd, " 83");
	   7'h54 : $fwrite (fd, " 84");
	   7'h55 : $fwrite (fd, " 85");
	   7'h56 : $fwrite (fd, " 86");
	   7'h57 : $fwrite (fd, " 87");
	   7'h58 : $fwrite (fd, " 88");
	   7'h59 : $fwrite (fd, " 89");
	   7'h5a : $fwrite (fd, " 90");
	   7'h5b : $fwrite (fd, " 91");
	   7'h5c : $fwrite (fd, " 92");
	   7'h5d : $fwrite (fd, " 93");
	   7'h5e : $fwrite (fd, " 94");
	   7'h5f : $fwrite (fd, " 95");
	   7'h60 : $fwrite (fd, " 96");
	   7'h61 : $fwrite (fd, " 97");
	   7'h62 : $fwrite (fd, " 98");
	   7'h63 : $fwrite (fd, " 99");
	   7'h64 : $fwrite (fd, " 100");
	   7'h65 : $fwrite (fd, " 101");
	   7'h66 : $fwrite (fd, " 102");
	   7'h67 : $fwrite (fd, " 103");
	   7'h68 : $fwrite (fd, " 104");
	   7'h69 : $fwrite (fd, " 105");
	   7'h6a : $fwrite (fd, " 106");
	   7'h6b : $fwrite (fd, " 107");
	   7'h6c : $fwrite (fd, " 108");
	   7'h6d : $fwrite (fd, " 109");
	   7'h6e : $fwrite (fd, " 110");
	   7'h6f : $fwrite (fd, " 111");
	   7'h70 : $fwrite (fd, " 112");
	   7'h71 : $fwrite (fd, " 113");
	   7'h72 : $fwrite (fd, " 114");
	   7'h73 : $fwrite (fd, " 115");
	   7'h74 : $fwrite (fd, " 116");
	   7'h75 : $fwrite (fd, " 117");
	   7'h76 : $fwrite (fd, " 118");
	   7'h77 : $fwrite (fd, " 119");
	   7'h78 : $fwrite (fd, " 120");
	   7'h79 : $fwrite (fd, " 121");
	   7'h7a : $fwrite (fd, " 122");
	   7'h7b : $fwrite (fd, " 123");
	   7'h7c : $fwrite (fd, " 124");
	   7'h7d : $fwrite (fd, " 125");
	   7'h7e : $fwrite (fd, " 126");
	   7'h7f : $fwrite (fd, " 127");
	   default:$fwrite (fd, " 128");
	 endcase
      end
   endtask

   task ozonerb;
      input  [5:0] rb;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (rb[5:0])
	   6'h10,
	     6'h17,
	     6'h1e,
	     6'h1f:   $fwrite (fd, " 129");
	   default: ozonerab({1'b1, rb}, fd);
	 endcase
      end
   endtask

   task ozonef3f4_iext;
      input  [1:0] foo;
      input [15:0]  im16;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (foo)
	   2'h0 :
             begin
		skyway({4{im16[15]}}, fd);
		skyway({4{im16[15]}}, fd);
		skyway(im16[15:12], fd);
		skyway(im16[11: 8], fd);
		skyway(im16[ 7: 4], fd);
		skyway(im16[ 3:0], fd);
		$fwrite (fd, " 130");
             end
	   2'h1 :
             begin
		$fwrite (fd, " 131");
		skyway(im16[15:12], fd);
		skyway(im16[11: 8], fd);
		skyway(im16[ 7: 4], fd);
		skyway(im16[ 3:0], fd);
             end
	   2'h2 :
             begin
		skyway({4{im16[15]}}, fd);
		skyway({4{im16[15]}}, fd);
		skyway(im16[15:12], fd);
		skyway(im16[11: 8], fd);
		skyway(im16[ 7: 4], fd);
		skyway(im16[ 3:0], fd);
		$fwrite (fd, " 132");
             end
	   2'h3 :
             begin
		$fwrite (fd, " 133");
		skyway(im16[15:12], fd);
		skyway(im16[11: 8], fd);
		skyway(im16[ 7: 4], fd);
		skyway(im16[ 3:0], fd);
             end
	 endcase
      end
   endtask

   task skyway;
      input  [ 3:0] hex;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (hex)
	   4'h0 : $fwrite (fd, " 134");
	   4'h1 : $fwrite (fd, " 135");
	   4'h2 : $fwrite (fd, " 136");
	   4'h3 : $fwrite (fd, " 137");
	   4'h4 : $fwrite (fd, " 138");
	   4'h5 : $fwrite (fd, " 139");
	   4'h6 : $fwrite (fd, " 140");
	   4'h7 : $fwrite (fd, " 141");
	   4'h8 : $fwrite (fd, " 142");
	   4'h9 : $fwrite (fd, " 143");
	   4'ha : $fwrite (fd, " 144");
	   4'hb : $fwrite (fd, " 145");
	   4'hc : $fwrite (fd, " 146");
	   4'hd : $fwrite (fd, " 147");
	   4'he : $fwrite (fd, " 148");
	   4'hf : $fwrite (fd, " 149");
	 endcase
      end
   endtask

   task ozonesr;
      input  [  15:0] foo;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (foo[11: 9])
	   3'h0 : $fwrite (fd, " 158");
	   3'h1 : $fwrite (fd, " 159");
	   3'h2 : $fwrite (fd, " 160");
	   3'h3 : $fwrite (fd, " 161");
	   3'h4 : $fwrite (fd, " 162");
	   3'h5 : $fwrite (fd, " 163");
	   3'h6 : $fwrite (fd, " 164");
	   3'h7 : $fwrite (fd, " 165");
	 endcase
      end
   endtask

   task ozonejk;
      input  k;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 if (k)
	   $fwrite (fd, " 166");
	 else
	   $fwrite (fd, " 167");
      end
   endtask

   task ozoneae;
      input  [   2:0]   ae;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (ae)
	   3'b000 : $fwrite (fd, " 168");
	   3'b001 : $fwrite (fd, " 169");
	   3'b010 : $fwrite (fd, " 170");
	   3'b011 : $fwrite (fd, " 171");
	   3'b100 : $fwrite (fd, " 172");
	   3'b101 : $fwrite (fd, " 173");
	   3'b110 : $fwrite (fd, " 174");
	   3'b111 : $fwrite (fd, " 175");
	 endcase
      end
   endtask

   task ozoneaee;
      input  [   2:0]   aee;
      input [`FD_BITS] 	fd;
      // verilator no_inline_task
      begin
	 case (aee)
	   3'b001,
	     3'b011,
	     3'b101,
	     3'b111 : $fwrite (fd, " 176");
	   3'b000 : $fwrite (fd, " 177");
	   3'b010 : $fwrite (fd, " 178");
	   3'b100 : $fwrite (fd, " 179");
	   3'b110 : $fwrite (fd, " 180");
	 endcase
      end
   endtask

   task ozoneape;
      input  [   2:0]   ape;
      input [`FD_BITS] 	fd;
      // verilator no_inline_task
      begin
	 case (ape)
	   3'b001,
	     3'b011,
	     3'b101,
	     3'b111 : $fwrite (fd, " 181");
	   3'b000 : $fwrite (fd, " 182");
	   3'b010 : $fwrite (fd, " 183");
	   3'b100 : $fwrite (fd, " 184");
	   3'b110 : $fwrite (fd, " 185");
	 endcase
      end
   endtask

   task ozonef1;
      input [  31:0] foo;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (foo[24:21])
	   4'h0 :
             if (foo[26])
               $fwrite (fd, " 186");
             else
               $fwrite (fd, " 187");
	   4'h1 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 188");
               2'b01 :  $fwrite (fd, " 189");
               2'b10 :  $fwrite (fd, " 190");
               2'b11 :  $fwrite (fd, " 191");
             endcase
	   4'h2 :  $fwrite (fd, " 192");
	   4'h3 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 193");
               2'b01 :  $fwrite (fd, " 194");
               2'b10 :  $fwrite (fd, " 195");
               2'b11 :  $fwrite (fd, " 196");
             endcase
	   4'h4 :
             if (foo[26])
               $fwrite (fd, " 197");
             else
               $fwrite (fd, " 198");
	   4'h5 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 199");
               2'b01 :  $fwrite (fd, " 200");
               2'b10 :  $fwrite (fd, " 201");
               2'b11 :  $fwrite (fd, " 202");
             endcase
	   4'h6 :  $fwrite (fd, " 203");
	   4'h7 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 204");
               2'b01 :  $fwrite (fd, " 205");
               2'b10 :  $fwrite (fd, " 206");
               2'b11 :  $fwrite (fd, " 207");
             endcase
	   4'h8 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 208");
               2'b01 :  $fwrite (fd, " 209");
               2'b10 :  $fwrite (fd, " 210");
               2'b11 :  $fwrite (fd, " 211");
             endcase
	   4'h9 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 212");
               2'b01 :  $fwrite (fd, " 213");
               2'b10 :  $fwrite (fd, " 214");
               2'b11 :  $fwrite (fd, " 215");
             endcase
	   4'ha :
             if (foo[25])
               $fwrite (fd, " 216");
             else
               $fwrite (fd, " 217");
	   4'hb :
             if (foo[25])
               $fwrite (fd, " 218");
             else
               $fwrite (fd, " 219");
	   4'hc :
             if (foo[26])
               $fwrite (fd, " 220");
             else
               $fwrite (fd, " 221");
	   4'hd :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 222");
               2'b01 :  $fwrite (fd, " 223");
               2'b10 :  $fwrite (fd, " 224");
               2'b11 :  $fwrite (fd, " 225");
             endcase
	   4'he :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 226");
               2'b01 :  $fwrite (fd, " 227");
               2'b10 :  $fwrite (fd, " 228");
               2'b11 :  $fwrite (fd, " 229");
             endcase
	   4'hf :
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 230");
               2'b01 :  $fwrite (fd, " 231");
               2'b10 :  $fwrite (fd, " 232");
               2'b11 :  $fwrite (fd, " 233");
             endcase
	 endcase
      end
   endtask

   task ozonef1e;
      input [  31:0] foo;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (foo[27:21])
	   7'h00:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 234");
		$fwrite (fd, " 235");
	     end
	   7'h01:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 236");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 237");
		$fwrite (fd, " 238");
	     end
	   7'h02:
	     $fwrite (fd, " 239");
	   7'h03:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 240");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 241");
		$fwrite (fd, " 242");
	     end
	   7'h04:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 243");
		$fwrite (fd," 244");
	     end
	   7'h05:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 245");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 246");
	     end
	   7'h06:
	     $fwrite (fd, " 247");
	   7'h07:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 248");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 249");
	     end
	   7'h08:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 250");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 251");
	     end
	   7'h09:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 252");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 253");
	     end
	   7'h0a:
	     begin
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 254");
	     end
	   7'h0b:
	     begin
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 255");
	     end
	   7'h0c:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 256");
	     end
	   7'h0d:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 257");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 258");
	     end
	   7'h0e:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 259");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 260");
	     end
	   7'h0f:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 261");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 262");
	     end
	   7'h10:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 263");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 264");
		$fwrite (fd, " 265");
		$fwrite (fd, " 266");
	     end
	   7'h11:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 267");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 268");
		$fwrite (fd, " 269");
		$fwrite (fd, " 270");
	     end
	   7'h12:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 271");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 272");
		$fwrite (fd, " 273");
		$fwrite (fd, " 274");
	     end
	   7'h13:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 275");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 276");
		$fwrite (fd, " 277");
		$fwrite (fd, " 278");
	     end
	   7'h14:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 279");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 280");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 281");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 282");
		$fwrite (fd, " 283");
		$fwrite (fd, " 284");
	     end
	   7'h15:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 285");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 286");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 287");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 288");
		$fwrite (fd, " 289");
		$fwrite (fd, " 290");
	     end
	   7'h16:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 291");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 292");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 293");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 294");
		$fwrite (fd, " 295");
		$fwrite (fd, " 296");
	     end
	   7'h17:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 297");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 298");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 299");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 300");
		$fwrite (fd, " 301");
		$fwrite (fd, " 302");
	     end
	   7'h18:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 303");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 304");
		$fwrite (fd, " 305");
		$fwrite (fd, " 306");
	     end
	   7'h19:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 307");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 308");
		$fwrite (fd, " 309");
		$fwrite (fd, " 310");
	     end
	   7'h1a:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 311");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 312");
		$fwrite (fd, " 313");
		$fwrite (fd, " 314");
	     end
	   7'h1b:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 315");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 316");
		$fwrite (fd, " 317");
		$fwrite (fd, " 318");
	     end
	   7'h1c:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 319");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 320");
		$fwrite (fd, " 321");
		$fwrite (fd, " 322");
	     end
	   7'h1d:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 323");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 324");
		$fwrite (fd, " 325");
		$fwrite (fd, " 326");
	     end
	   7'h1e:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 327");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 328");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 329");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 330");
		$fwrite (fd, " 331");
		$fwrite (fd, " 332");
	     end
	   7'h1f:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 333");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 334");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 335");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 336");
		$fwrite (fd, " 337");
		$fwrite (fd, " 338");
	     end
	   7'h20:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 339");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 340");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 341");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 342");
		$fwrite (fd, " 343");
		$fwrite (fd, " 344");
	     end
	   7'h21:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 345");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 346");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 347");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 348");
		$fwrite (fd, " 349");
		$fwrite (fd, " 350");
	     end
	   7'h22:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 351");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 352");
		$fwrite (fd, " 353");
		$fwrite (fd, " 354");
	     end
	   7'h23:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 355");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 356");
		$fwrite (fd, " 357");
		$fwrite (fd, " 358");
	     end
	   7'h24:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 359");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 360");
		$fwrite (fd, " 361");
		$fwrite (fd, " 362");
	     end
	   7'h25:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 363");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 364");
		$fwrite (fd, " 365");
		$fwrite (fd, " 366");
	     end
	   7'h26:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 367");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 368");
		$fwrite (fd, " 369");
		$fwrite (fd, " 370");
	     end
	   7'h27:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 371");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 372");
		$fwrite (fd, " 373");
		$fwrite (fd, " 374");
	     end
	   7'h28:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 375");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 376");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 377");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 378");
		$fwrite (fd, " 379");
		$fwrite (fd, " 380");
	     end
	   7'h29:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 381");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 382");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 383");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 384");
		$fwrite (fd, " 385");
		$fwrite (fd, " 386");
	     end
	   7'h2a:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 387");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 388");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 389");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 390");
		$fwrite (fd, " 391");
		$fwrite (fd, " 392");
	     end
	   7'h2b:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 393");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 394");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 395");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 396");
		$fwrite (fd, " 397");
		$fwrite (fd, " 398");
	     end
	   7'h2c:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 399");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 400");
		$fwrite (fd, " 401");
		$fwrite (fd, " 402");
	     end
	   7'h2d:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 403");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 404");
		$fwrite (fd, " 405");
		$fwrite (fd, " 406");
	     end
	   7'h2e:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 407");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 408");
		$fwrite (fd, " 409");
		$fwrite (fd, " 410");
	     end
	   7'h2f:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 411");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 412");
		$fwrite (fd, " 413");
		$fwrite (fd, " 414");
	     end
	   7'h30:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 415");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 416");
		$fwrite (fd, " 417");
		$fwrite (fd, " 418");
	     end
	   7'h31:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 419");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 420");
		$fwrite (fd, " 421");
		$fwrite (fd, " 422");
	     end
	   7'h32:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 423");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 424");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 425");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 426");
		$fwrite (fd, " 427");
		$fwrite (fd, " 428");
	     end
	   7'h33:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 429");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 430");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 431");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 432");
		$fwrite (fd, " 433");
		$fwrite (fd, " 434");
	     end
	   7'h34:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 435");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 436");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 437");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 438");
		$fwrite (fd, " 439");
		$fwrite (fd, " 440");
	     end
	   7'h35:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 441");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 442");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 443");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 444");
		$fwrite (fd, " 445");
		$fwrite (fd, " 446");
	     end
	   7'h36:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 447");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 448");
		$fwrite (fd, " 449");
		$fwrite (fd, " 450");
	     end
	   7'h37:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 451");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 452");
		$fwrite (fd, " 453");
		$fwrite (fd, " 454");
	     end
	   7'h38:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 455");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 456");
		$fwrite (fd, " 457");
	     end
	   7'h39:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 458");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 459");
		$fwrite (fd, " 460");
	     end
	   7'h3a:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 461");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 462");
		$fwrite (fd, " 463");
	     end
	   7'h3b:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 464");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 465");
		$fwrite (fd, " 466");
	     end
	   7'h3c:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 467");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 468");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 469");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 470");
		$fwrite (fd, " 471");
	     end
	   7'h3d:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 472");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 473");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 474");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 475");
		$fwrite (fd, " 476");
	     end
	   7'h3e:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 477");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 478");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 479");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 480");
		$fwrite (fd, " 481");
	     end
	   7'h3f:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 482");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 483");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 484");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 485");
		$fwrite (fd, " 486");
	     end
	   7'h40:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 487");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 488");
		$fwrite (fd, " 489");
		$fwrite (fd, " 490");
	     end
	   7'h41:
	     begin
		$fwrite (fd, " 491");
		$fwrite (fd, " 492");
	     end
	   7'h42:
	     begin
		$fwrite (fd, " 493");
		$fwrite (fd, " 494");
	     end
	   7'h43:
	     begin
		$fwrite (fd, " 495");
		$fwrite (fd, " 496");
	     end
	   7'h44:
	     begin
		$fwrite (fd, " 497");
		$fwrite (fd, " 498");
	     end
	   7'h45:
	     $fwrite (fd, " 499");
	   7'h46:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 500");
		$fwrite (fd, " 501");
		$fwrite (fd, " 502");
	     end
	   7'h47:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 503");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 504");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 505");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 506");
		$fwrite (fd, " 507");
		$fwrite (fd, " 508");
	     end
	   7'h48:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 509");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 510");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 511");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 512");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 513");
	     end
	   7'h49:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 514");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 515");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 516");
	     end
	   7'h4a:
             $fwrite (fd," 517");
	   7'h4b:
             $fwrite (fd, " 518");
	   7'h4c:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 519");
		$fwrite (fd, " 520");
		$fwrite (fd, " 521");
	     end
	   7'h4d:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 522");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 523");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 524");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 525");
		$fwrite (fd, " 526");
		$fwrite (fd, " 527");
	     end
	   7'h4e:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 528");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 529");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 530");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 531");
	     end
	   7'h4f:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 532");
	     end
	   7'h50:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 533");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 534");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 535");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 536");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 537");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 538");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 539");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 540");
	     end
	   7'h51:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 541");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 542");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 543");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 544");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 545");
	     end
	   7'h52:
	     $fwrite (fd, " 546");
	   7'h53:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd, " 547");
	     end
	   7'h54:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 548");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 549");
	     end
	   7'h55:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 550");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 551");
	     end
	   7'h56:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 552");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 553");
		$fwrite (fd, " 554");
	     end
	   7'h57:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 555");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 556");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 557");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 558");
	     end
	   7'h58:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd, " 559");
	     end
	   7'h59:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 560");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 561");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 562");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 563");
	     end
	   7'h5a:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 564");
		ozoneae(foo[17:15], fd);
		$fwrite (fd, " 565");
	     end
	   7'h5b:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 566");
		ozoneae(foo[17:15], fd);
		$fwrite (fd, " 567");
	     end
	   7'h5c:
	     begin
		$fwrite (fd," 568");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 569");
		$fwrite (fd," 570");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 571");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 572");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd, " 573");
	     end
	   7'h5d:
	     begin
		$fwrite (fd," 574");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 575");
		$fwrite (fd," 576");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 577");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 578");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd, " 579");
	     end
	   7'h5e:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 580");
		ozoneae(foo[17:15], fd);
		$fwrite (fd, " 581");
	     end
	   7'h5f:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 582");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 583");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 584");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 585");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 586");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 587");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 588");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 589");
	     end
	   7'h60:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 590");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 591");
	     end
	   7'h61:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 592");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 593");
	     end
	   7'h62:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 594");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 595");
	     end
	   7'h63:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 596");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 597");
	     end
	   7'h64:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 598");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 599");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 600");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 601");
	     end
	   7'h65:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 602");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 603");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 604");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 605");
	     end
	   7'h66:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 606");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 607");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 608");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 609");
	     end
	   7'h67:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 610");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 611");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 612");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 613");
	     end
	   7'h68:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 614");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 615");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 616");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 617");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 618");
		ozoneape(foo[17:15], fd);
	     end
	   7'h69:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 619");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 620");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 621");
	     end
	   7'h6a:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 622");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 623");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 624");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 625");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 626");
		ozoneae(foo[17:15], fd);
	     end
	   7'h6b:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 627");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 628");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 629");
	     end
	   7'h6c:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 630");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 631");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 632");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 633");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 634");
		ozoneae(foo[17:15], fd);
	     end
	   7'h6d:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 635");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 636");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 637");
	     end
	   7'h6e:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 638");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 639");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 640");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 641");
	     end
	   7'h6f:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 642");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 643");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 644");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 645");
	     end
	   7'h70:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 646");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 647");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 648");
		ozoneae(foo[17:15], fd);
		$fwrite (fd, " 649");
	     end
	   7'h71:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 650");
		ozoneae(foo[17:15], fd);
		$fwrite (fd, " 651");
	     end
	   7'h72:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 652");
		ozoneae(foo[17:15], fd);
		$fwrite (fd, " 653");
	     end
	   7'h73:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 654");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 655");
		ozoneae(foo[17:15], fd);
	     end
	   7'h74:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 656");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 657");
		ozoneae(foo[17:15], fd);
	     end
	   7'h75:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 658");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 659");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 660");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 661");
		$fwrite (fd, " 662");
		$fwrite (fd, " 663");
	     end
	   7'h76:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 664");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 665");
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 666");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 667");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 668");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 669");
	     end
	   7'h77:
	     begin
		ozoneaee(foo[20:18], fd);
		$fwrite (fd," 670");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 671");
		ozoneaee(foo[17:15], fd);
		$fwrite (fd," 672");
		ozoneape(foo[20:18], fd);
		$fwrite (fd," 673");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 674");
		ozoneape(foo[17:15], fd);
		$fwrite (fd," 675");
	     end
	   7'h78,
	     7'h79,
	     7'h7a,
	     7'h7b,
	     7'h7c,
	     7'h7d,
	     7'h7e,
	     7'h7f:
               $fwrite (fd," 676");
	 endcase
      end
   endtask

   task ozonef2;
      input [  31:0] foo;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      begin
	 case (foo[24:21])
	   4'h0 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 677");
               2'b01 :  $fwrite (fd," 678");
               2'b10 :  $fwrite (fd," 679");
               2'b11 :  $fwrite (fd," 680");
             endcase
	   4'h1 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 681");
               2'b01 :  $fwrite (fd," 682");
               2'b10 :  $fwrite (fd," 683");
               2'b11 :  $fwrite (fd," 684");
             endcase
	   4'h2 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 685");
               2'b01 :  $fwrite (fd," 686");
               2'b10 :  $fwrite (fd," 687");
               2'b11 :  $fwrite (fd," 688");
             endcase
	   4'h3 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 689");
               2'b01 :  $fwrite (fd," 690");
               2'b10 :  $fwrite (fd," 691");
               2'b11 :  $fwrite (fd," 692");
             endcase
	   4'h4 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 693");
               2'b01 :  $fwrite (fd," 694");
               2'b10 :  $fwrite (fd," 695");
               2'b11 :  $fwrite (fd," 696");
             endcase
	   4'h5 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 697");
               2'b01 :  $fwrite (fd," 698");
               2'b10 :  $fwrite (fd," 699");
               2'b11 :  $fwrite (fd," 700");
             endcase
	   4'h6 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 701");
               2'b01 :  $fwrite (fd," 702");
               2'b10 :  $fwrite (fd," 703");
               2'b11 :  $fwrite (fd," 704");
             endcase
	   4'h7 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 705");
               2'b01 :  $fwrite (fd," 706");
               2'b10 :  $fwrite (fd," 707");
               2'b11 :  $fwrite (fd," 708");
             endcase
	   4'h8 :
             if (foo[26])
               $fwrite (fd," 709");
             else
               $fwrite (fd," 710");
	   4'h9 :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 711");
               2'b01 :  $fwrite (fd," 712");
               2'b10 :  $fwrite (fd," 713");
               2'b11 :  $fwrite (fd," 714");
             endcase
	   4'ha :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 715");
               2'b01 :  $fwrite (fd," 716");
               2'b10 :  $fwrite (fd," 717");
               2'b11 :  $fwrite (fd," 718");
             endcase
	   4'hb :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 719");
               2'b01 :  $fwrite (fd," 720");
               2'b10 :  $fwrite (fd," 721");
               2'b11 :  $fwrite (fd," 722");
             endcase
	   4'hc :
             if (foo[26])
               $fwrite (fd," 723");
             else
               $fwrite (fd," 724");
	   4'hd :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 725");
               2'b01 :  $fwrite (fd," 726");
               2'b10 :  $fwrite (fd," 727");
               2'b11 :  $fwrite (fd," 728");
             endcase
	   4'he :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 729");
               2'b01 :  $fwrite (fd," 730");
               2'b10 :  $fwrite (fd," 731");
               2'b11 :  $fwrite (fd," 732");
             endcase
	   4'hf :
             case (foo[26:25])
               2'b00 :  $fwrite (fd," 733");
               2'b01 :  $fwrite (fd," 734");
               2'b10 :  $fwrite (fd," 735");
               2'b11 :  $fwrite (fd," 736");
             endcase
	 endcase
      end
   endtask

   task ozonef2e;
      input [  31:0] foo;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 casez (foo[25:21])
	   5'h00 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 737");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 738");
	     end
	   5'h01 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 739");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 740");
	     end
	   5'h02 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 741");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 742");
	     end
	   5'h03 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 743");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 744");
	     end
	   5'h04 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 745");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 746");
	     end
	   5'h05 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 747");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 748");
	     end
	   5'h06 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 749");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 750");
	     end
	   5'h07 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 751");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 752");
	     end
	   5'h08 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 753");
		if (foo[ 6])
		  $fwrite (fd," 754");
		else
		  $fwrite (fd," 755");
	     end
	   5'h09 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 756");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 757");
	     end
	   5'h0a :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 758");
		ozoneae(foo[17:15], fd);
	     end
	   5'h0b :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 759");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 760");
	     end
	   5'h0c :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 761");
	     end
	   5'h0d :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 762");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 763");
	     end
	   5'h0e :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 764");
		ozoneae(foo[17:15], fd);
	     end
	   5'h0f :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 765");
		ozoneae(foo[17:15], fd);
	     end
	   5'h10 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 766");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 767");
	     end
	   5'h11 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 768");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 769");
	     end
	   5'h18 :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 770");
		if (foo[ 6])
		  $fwrite (fd," 771");
		else
		  $fwrite (fd," 772");
	     end
	   5'h1a :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 773");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 774");
	     end
	   5'h1b :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 775");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 776");
		if (foo[ 6])
		  $fwrite (fd," 777");
		else
		  $fwrite (fd," 778");
		$fwrite (fd," 779");
	     end
	   5'h1c :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 780");
	     end
	   5'h1d :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 781");
		if (foo[ 6])
		  $fwrite (fd," 782");
		else
		  $fwrite (fd," 783");
		$fwrite (fd," 784");
	     end
	   5'h1e :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 785");
		if (foo[ 6])
		  $fwrite (fd," 786");
		else
		  $fwrite (fd," 787");
		$fwrite (fd," 788");
	     end
	   5'h1f :
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 789");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 790");
		if (foo[ 6])
		  $fwrite (fd," 791");
		else
		  $fwrite (fd," 792");
		$fwrite (fd," 793");
	     end
	   default :
             $fwrite (fd," 794");
	 endcase
      end
   endtask

   task ozonef3e;
      input [  31:0] foo;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (foo[25:21])
	   5'h00,
	     5'h01,
	     5'h02:
	       begin
		  ozoneae(foo[20:18], fd);
		  case (foo[22:21])
		    2'h0: $fwrite (fd," 795");
		    2'h1: $fwrite (fd," 796");
		    2'h2: $fwrite (fd," 797");
		  endcase
		  ozoneae(foo[17:15], fd);
		  $fwrite (fd," 798");
		  if (foo[ 9])
		    ozoneae(foo[ 8: 6], fd);
		  else
		    ozonef3e_te(foo[ 8: 6], fd);
		  $fwrite (fd," 799");
	       end
	   5'h08,
	     5'h09,
	     5'h0d,
	     5'h0e,
	     5'h0f:
	       begin
		  ozoneae(foo[20:18], fd);
		  $fwrite (fd," 800");
		  ozoneae(foo[17:15], fd);
		  case (foo[23:21])
		    3'h0: $fwrite (fd," 801");
		    3'h1: $fwrite (fd," 802");
		    3'h5: $fwrite (fd," 803");
		    3'h6: $fwrite (fd," 804");
		    3'h7: $fwrite (fd," 805");
		  endcase
		  if (foo[ 9])
		    ozoneae(foo[ 8: 6], fd);
		  else
		    ozonef3e_te(foo[ 8: 6], fd);
	       end
	   5'h0a,
	     5'h0b:
	       begin
		  ozoneae(foo[17:15], fd);
		  if (foo[21])
		    $fwrite (fd," 806");
		  else
		    $fwrite (fd," 807");
		  if (foo[ 9])
		    ozoneae(foo[ 8: 6], fd);
		  else
		    ozonef3e_te(foo[ 8: 6], fd);
	       end
	   5'h0c:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 808");
		if (foo[ 9])
		  ozoneae(foo[ 8: 6], fd);
		else
		  ozonef3e_te(foo[ 8: 6], fd);
		$fwrite (fd," 809");
		ozoneae(foo[17:15], fd);
	     end
	   5'h10,
	     5'h11,
	     5'h12,
	     5'h13:
	       begin
		  ozoneae(foo[20:18], fd);
		  $fwrite (fd," 810");
		  ozoneae(foo[17:15], fd);
		  case (foo[22:21])
		    2'h0,
		      2'h2:
			$fwrite (fd," 811");
		    2'h1,
		      2'h3:
			$fwrite (fd," 812");
		  endcase
		  ozoneae(foo[ 8: 6], fd);
		  $fwrite (fd," 813");
		  ozoneae((foo[20:18]+1), fd);
		  $fwrite (fd," 814");
		  ozoneae((foo[17:15]+1), fd);
		  case (foo[22:21])
		    2'h0,
		      2'h3:
			$fwrite (fd," 815");
		    2'h1,
		      2'h2:
			$fwrite (fd," 816");
		  endcase
		  ozoneae((foo[ 8: 6]+1), fd);
	       end
	   5'h18:
	     begin
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 817");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 818");
		ozoneae(foo[ 8: 6], fd);
		$fwrite (fd," 819");
		ozoneae(foo[20:18], fd);
		$fwrite (fd," 820");
		ozoneae(foo[17:15], fd);
		$fwrite (fd," 821");
		ozoneae(foo[ 8: 6], fd);
	     end
	   default :
             $fwrite (fd," 822");
	 endcase
      end
   endtask
   task ozonef3e_te;
      input  [   2:0]   te;
      input [`FD_BITS] 	fd;
      // verilator no_inline_task
      begin
	 case (te)
	   3'b100 : $fwrite (fd, " 823");
	   3'b101 : $fwrite (fd, " 824");
	   3'b110 : $fwrite (fd, " 825");
	   default: $fwrite (fd, " 826");
	 endcase
      end
   endtask
   task ozonearm;
      input  [   2:0]   ate;
      input [`FD_BITS] 	fd;
      // verilator no_inline_task
      begin
	 case (ate)
	   3'b000 : $fwrite (fd, " 827");
	   3'b001 : $fwrite (fd, " 828");
	   3'b010 : $fwrite (fd, " 829");
	   3'b011 : $fwrite (fd, " 830");
	   3'b100 : $fwrite (fd, " 831");
	   3'b101 : $fwrite (fd, " 832");
	   3'b110 : $fwrite (fd, " 833");
	   3'b111 : $fwrite (fd, " 834");
	 endcase
      end
   endtask
   task ozonebmuop;
      input  [ 4:0] f4;
      input [`FD_BITS]  fd;
      // verilator no_inline_task
      begin
	 case (f4[ 4:0])
	   5'h00,
	     5'h04 :
               $fwrite (fd, " 835");
	   5'h01,
	     5'h05 :
               $fwrite (fd, " 836");
	   5'h02,
	     5'h06 :
               $fwrite (fd, " 837");
	   5'h03,
	     5'h07 :
               $fwrite (fd, " 838");
	   5'h08,
	     5'h18 :
               $fwrite (fd, " 839");
	   5'h09,
	     5'h19 :
               $fwrite (fd, " 840");
	   5'h0a,
	     5'h1a :
               $fwrite (fd, " 841");
	   5'h0b :
             $fwrite (fd, " 842");
	   5'h1b :
             $fwrite (fd, " 843");
	   5'h0c,
	     5'h1c :
               $fwrite (fd, " 844");
	   5'h0d,
	     5'h1d :
               $fwrite (fd, " 845");
	   5'h1e :
             $fwrite (fd, " 846");
	 endcase
      end
   endtask
   task ozonef3;
      input  [  31:0] foo;
      input [`FD_BITS]    fd;
      reg 		  nacho;
      // verilator no_inline_task
      begin : f3_body
	 nacho = 1'b0;
	 case (foo[24:21])
	   4'h0:
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 847");
               2'b01 :  $fwrite (fd, " 848");
               2'b10 :  $fwrite (fd, " 849");
               2'b11 :  $fwrite (fd, " 850");
             endcase
	   4'h1:
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 851");
               2'b01 :  $fwrite (fd, " 852");
               2'b10 :  $fwrite (fd, " 853");
               2'b11 :  $fwrite (fd, " 854");
             endcase
	   4'h2:
             case (foo[26:25])
               2'b00 :  $fwrite (fd, " 855");
               2'b01 :  $fwrite (fd, " 856");
               2'b10 :  $fwrite (fd, " 857");
               2'b11 :  $fwrite (fd, " 858");
             endcase
	   4'h8,
	     4'h9,
	     4'hd,
	     4'he,
	     4'hf :
               case (foo[26:25])
		 2'b00 :  $fwrite (fd, " 859");
		 2'b01 :  $fwrite (fd, " 860");
		 2'b10 :  $fwrite (fd, " 861");
		 2'b11 :  $fwrite (fd, " 862");
               endcase
	   4'ha,
	     4'hb :
               if (foo[25])
		 $fwrite (fd, " 863");
               else
		 $fwrite (fd, " 864");
	   4'hc :
             if (foo[26])
               $fwrite (fd, " 865");
             else
               $fwrite (fd, " 866");
	   default :
	     begin
		$fwrite (fd, " 867");
		nacho = 1'b1;
	     end
	 endcase
	 if (~nacho)
	   begin
	      case (foo[24:21])
		4'h8 :
		  $fwrite (fd, " 868");
		4'h9 :
		  $fwrite (fd, " 869");
		4'ha,
		  4'he :
		    $fwrite (fd, " 870");
		4'hb,
		  4'hf :
		    $fwrite (fd, " 871");
		4'hd :
		  $fwrite (fd, " 872");
	      endcase
	      if (foo[20])
		case (foo[18:16])
		  3'b000 : $fwrite (fd, " 873");
		  3'b100 : $fwrite (fd, " 874");
		  default: $fwrite (fd, " 875");
		endcase
	      else
		ozoneae(foo[18:16], fd);
	      if (foo[24:21] === 4'hc)
		if (foo[25])
		  $fwrite (fd, " 876");
		else
		  $fwrite (fd, " 877");
	      case (foo[24:21])
		4'h0,
		  4'h1,
		  4'h2:
		    $fwrite (fd, " 878");
	      endcase
	   end
      end
   endtask
   task ozonerx;
      input  [  31:0] foo;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 case (foo[19:18])
	   2'h0 :  $fwrite (fd, " 879");
	   2'h1 :  $fwrite (fd, " 880");
	   2'h2 :  $fwrite (fd, " 881");
	   2'h3 :  $fwrite (fd, " 882");
	 endcase
	 case (foo[17:16])
	   2'h1 :  $fwrite (fd, " 883");
	   2'h2 :  $fwrite (fd, " 884");
	   2'h3 :  $fwrite (fd, " 885");
	 endcase
      end
   endtask
   task ozonerme;
      input  [  2:0] rme;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (rme)
	   3'h0 :  $fwrite (fd, " 886");
	   3'h1 :  $fwrite (fd, " 887");
	   3'h2 :  $fwrite (fd, " 888");
	   3'h3 :  $fwrite (fd, " 889");
	   3'h4 :  $fwrite (fd, " 890");
	   3'h5 :  $fwrite (fd, " 891");
	   3'h6 :  $fwrite (fd, " 892");
	   3'h7 :  $fwrite (fd, " 893");
	 endcase
      end
   endtask
   task ozoneye;
      input  [5:0] ye;
      input 	      l;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 $fwrite (fd, " 894");
	 ozonerme(ye[5:3], fd);
	 case ({ye[ 2:0], l})
	   4'h2,
	     4'ha:  $fwrite (fd, " 895");
	   4'h4,
	     4'hb:  $fwrite (fd, " 896");
	   4'h6,
	     4'he:  $fwrite (fd, " 897");
	   4'h8,
	     4'hc:  $fwrite (fd, " 898");
	 endcase
      end
   endtask
   task ozonef1e_ye;
      input  [5:0] ye;
      input 	      l;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 $fwrite (fd, " 899");
	 ozonerme(ye[5:3], fd);
	 ozonef1e_inc_dec(ye[5:0], l , fd);
      end
   endtask
   task ozonef1e_h;
      input  [  2:0] e;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 if (e[ 2:0] <= 3'h4)
	   $fwrite (fd, " 900");
      end
   endtask
   task ozonef1e_inc_dec;
      input  [5:0] ye;
      input 	      l;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 case ({ye[ 2:0], l})
	   4'h2,
	     4'h3,
	     4'ha:  $fwrite (fd, " 901");
	   4'h4,
	     4'h5,
	     4'hb:  $fwrite (fd, " 902");
	   4'h6,
	     4'h7,
	     4'he:  $fwrite (fd, " 903");
	   4'h8,
	     4'h9,
	     4'hc:  $fwrite (fd, " 904");
	   4'hf:  $fwrite (fd, " 905");
	 endcase
      end
   endtask
   task ozonef1e_hl;
      input  [  2:0] e;
      input           l;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 case ({e[ 2:0], l})
	   4'h0,
	     4'h2,
	     4'h4,
	     4'h6,
	     4'h8: $fwrite (fd, " 906");
	   4'h1,
	     4'h3,
	     4'h5,
	     4'h7,
	     4'h9: $fwrite (fd, " 907");
	 endcase
      end
   endtask
   task ozonexe;
      input  [  3:0] xe;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (xe[3])
	   1'b0 :  $fwrite (fd, " 908");
	   1'b1 :  $fwrite (fd, " 909");
	 endcase
	 case (xe[ 2:0])
	   3'h1,
	     3'h5:  $fwrite (fd, " 910");
	   3'h2,
	     3'h6:  $fwrite (fd, " 911");
	   3'h3,
	     3'h7:  $fwrite (fd, " 912");
	   3'h4:  $fwrite (fd, " 913");
	 endcase
      end
   endtask
   task ozonerp;
      input  [  2:0] rp;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (rp)
	   3'h0 :  $fwrite (fd, " 914");
	   3'h1 :  $fwrite (fd, " 915");
	   3'h2 :  $fwrite (fd, " 916");
	   3'h3 :  $fwrite (fd, " 917");
	   3'h4 :  $fwrite (fd, " 918");
	   3'h5 :  $fwrite (fd, " 919");
	   3'h6 :  $fwrite (fd, " 920");
	   3'h7 :  $fwrite (fd, " 921");
	 endcase
      end
   endtask
   task ozonery;
      input  [  3:0] ry;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (ry)
	   4'h0 :  $fwrite (fd, " 922");
	   4'h1 :  $fwrite (fd, " 923");
	   4'h2 :  $fwrite (fd, " 924");
	   4'h3 :  $fwrite (fd, " 925");
	   4'h4 :  $fwrite (fd, " 926");
	   4'h5 :  $fwrite (fd, " 927");
	   4'h6 :  $fwrite (fd, " 928");
	   4'h7 :  $fwrite (fd, " 929");
	   4'h8 :  $fwrite (fd, " 930");
	   4'h9 :  $fwrite (fd, " 931");
	   4'ha :  $fwrite (fd, " 932");
	   4'hb :  $fwrite (fd, " 933");
	   4'hc :  $fwrite (fd, " 934");
	   4'hd :  $fwrite (fd, " 935");
	   4'he :  $fwrite (fd, " 936");
	   4'hf :  $fwrite (fd, " 937");
	 endcase
      end
   endtask
   task ozonearx;
      input  [  15:0] foo;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 case (foo[1:0])
	   2'h0 :  $fwrite (fd, " 938");
	   2'h1 :  $fwrite (fd, " 939");
	   2'h2 :  $fwrite (fd, " 940");
	   2'h3 :  $fwrite (fd, " 941");
	 endcase
      end
   endtask
   task ozonef3f4imop;
      input  [  4:0]   f3f4iml;
      input [`FD_BITS]     fd;
      // verilator no_inline_task
      begin
	 casez (f3f4iml)
	   5'b000??: $fwrite (fd, " 942");
	   5'b001??: $fwrite (fd, " 943");
	   5'b?10??: $fwrite (fd, " 944");
	   5'b0110?: $fwrite (fd, " 945");
	   5'b01110: $fwrite (fd, " 946");
	   5'b01111: $fwrite (fd, " 947");
	   5'b10???: $fwrite (fd, " 948");
	   5'b11100: $fwrite (fd, " 949");
	   5'b11101: $fwrite (fd, " 950");
	   5'b11110: $fwrite (fd, " 951");
	   5'b11111: $fwrite (fd, " 952");
	 endcase
      end
   endtask
   task ozonecon;
      input  [  4:0] con;
      input [`FD_BITS]   fd;
      // verilator no_inline_task
      begin
	 case (con)
	   5'h00 :  $fwrite (fd, " 953");
	   5'h01 :  $fwrite (fd, " 954");
	   5'h02 :  $fwrite (fd, " 955");
	   5'h03 :  $fwrite (fd, " 956");
	   5'h04 :  $fwrite (fd, " 957");
	   5'h05 :  $fwrite (fd, " 958");
	   5'h06 :  $fwrite (fd, " 959");
	   5'h07 :  $fwrite (fd, " 960");
	   5'h08 :  $fwrite (fd, " 961");
	   5'h09 :  $fwrite (fd, " 962");
	   5'h0a :  $fwrite (fd, " 963");
	   5'h0b :  $fwrite (fd, " 964");
	   5'h0c :  $fwrite (fd, " 965");
	   5'h0d :  $fwrite (fd, " 966");
	   5'h0e :  $fwrite (fd, " 967");
	   5'h0f :  $fwrite (fd, " 968");
	   5'h10 :  $fwrite (fd, " 969");
	   5'h11 :  $fwrite (fd, " 970");
	   5'h12 :  $fwrite (fd, " 971");
	   5'h13 :  $fwrite (fd, " 972");
	   5'h14 :  $fwrite (fd, " 973");
	   5'h15 :  $fwrite (fd, " 974");
	   5'h16 :  $fwrite (fd, " 975");
	   5'h17 :  $fwrite (fd, " 976");
	   5'h18 :  $fwrite (fd, " 977");
	   5'h19 :  $fwrite (fd, " 978");
	   5'h1a :  $fwrite (fd, " 979");
	   5'h1b :  $fwrite (fd, " 980");
	   5'h1c :  $fwrite (fd, " 981");
	   5'h1d :  $fwrite (fd, " 982");
	   5'h1e :  $fwrite (fd, " 983");
	   5'h1f :  $fwrite (fd, " 984");
	 endcase
      end
   endtask
   task ozonedr;
      input  [  15:0] foo;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 case (foo[ 9: 6])
	   4'h0 :  $fwrite (fd, " 985");
	   4'h1 :  $fwrite (fd, " 986");
	   4'h2 :  $fwrite (fd, " 987");
	   4'h3 :  $fwrite (fd, " 988");
	   4'h4 :  $fwrite (fd, " 989");
	   4'h5 :  $fwrite (fd, " 990");
	   4'h6 :  $fwrite (fd, " 991");
	   4'h7 :  $fwrite (fd, " 992");
	   4'h8 :  $fwrite (fd, " 993");
	   4'h9 :  $fwrite (fd, " 994");
	   4'ha :  $fwrite (fd, " 995");
	   4'hb :  $fwrite (fd, " 996");
	   4'hc :  $fwrite (fd, " 997");
	   4'hd :  $fwrite (fd, " 998");
	   4'he :  $fwrite (fd, " 999");
	   4'hf :  $fwrite (fd, " 1000");
	 endcase
      end
   endtask
   task ozoneshift;
      input  [  15:0] foo;
      input [`FD_BITS]    fd;
      // verilator no_inline_task
      begin
	 case (foo[ 4: 3])
	   2'h0 :  $fwrite (fd, " 1001");
	   2'h1 :  $fwrite (fd, " 1002");
	   2'h2 :  $fwrite (fd, " 1003");
	   2'h3 :  $fwrite (fd, " 1004");
	 endcase
      end
   endtask
   task ozoneacc;
      input            foo;
      input [`FD_BITS]     fd;
      // verilator no_inline_task
      begin
	 case (foo)
	   2'h0 :  $fwrite (fd, " 1005");
	   2'h1 :  $fwrite (fd, " 1006");
	 endcase
      end
   endtask
   task ozonehl;
      input            foo;
      input [`FD_BITS]     fd;
      // verilator no_inline_task
      begin
	 case (foo)
	   2'h0 :  $fwrite (fd, " 1007");
	   2'h1 :  $fwrite (fd, " 1008");
	 endcase
      end
   endtask
   task dude;
      input [`FD_BITS] fd;
      // verilator no_inline_task
      $fwrite(fd," dude");
   endtask

   task big_case;
      input  [  `FD_BITS] fd;
      input [  31:0]  foo;
      // verilator no_inline_task
      begin
	 $fwrite(fd," 1009");
	 if (&foo === 1'bx)
	   $fwrite(fd, " 1010");
	 else
	   casez ( {foo[31:26], foo[19:15], foo[5:0]} )
             17'b00_111?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1011");
		  ozoneacc(~foo[26], fd);
		  ozonehl(foo[20], fd);
		  $fwrite (fd, " 1012");
		  ozonerx(foo, fd);
		  dude(fd);
		  $fwrite (fd, " 1013");
               end
             17'b01_001?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1014");
		  ozonerx(foo, fd);
		  $fwrite (fd, " 1015");
		  $fwrite (fd, " 1016:%x", foo[20]);
		  ozonehl(foo[20], fd);
		  dude(fd);
		  $fwrite (fd, " 1017");
               end
             17'b10_100?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1018");
		  ozonerx(foo, fd);
		  $fwrite (fd, " 1019");
		  $fwrite (fd, " 1020");
		  ozonehl(foo[20], fd);
		  dude(fd);
		  $fwrite (fd, " 1021");
               end
             17'b10_101?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1022");
		  if (foo[20])
		    begin
		       $fwrite (fd, " 1023");
		       ozoneacc(foo[18], fd);
		       $fwrite (fd, " 1024");
		       $fwrite (fd, " 1025");
		       if (foo[19])
			 $fwrite (fd, " 1026");
		       else
			 $fwrite (fd, " 1027");
		    end
		  else
		    ozonerx(foo, fd);
		  dude(fd);
		  $fwrite (fd, " 1028");
               end
             17'b10_110?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1029");
		  $fwrite (fd, " 1030");
		  ozonehl(foo[20], fd);
		  $fwrite (fd, " 1031");
		  ozonerx(foo, fd);
		  dude(fd);
		  $fwrite (fd, " 1032");
               end
             17'b10_111?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1033");
		  $fwrite (fd, " 1034");
		  ozonehl(foo[20], fd);
		  $fwrite (fd, " 1035");
		  ozonerx(foo, fd);
		  dude(fd);
		  $fwrite (fd, " 1036");
               end
             17'b11_001?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1037");
		  ozonerx(foo, fd);
		  $fwrite (fd, " 1038");
		  $fwrite (fd, " 1039");
		  ozonehl(foo[20], fd);
		  dude(fd);
		  $fwrite (fd, " 1040");
               end
             17'b11_111?_?_????_??_???? :
               begin
		  ozonef1(foo, fd);
		  $fwrite (fd, " 1041");
		  $fwrite (fd, " 1042");
		  ozonerx(foo, fd);
		  $fwrite (fd, " 1043");
		  if (foo[20])
		    $fwrite (fd, " 1044");
		  else
		    $fwrite (fd, " 1045");
		  dude(fd);
		  $fwrite (fd, " 1046");
               end
             17'b00_10??_?_????_?1_1111 :
               casez (foo[11: 5])
		 7'b??_0_010_0:
		   begin
		      $fwrite (fd, " 1047");
		      ozonecon(foo[14:10], fd);
		      $fwrite (fd, " 1048");
		      ozonef1e(foo, fd);
		      dude(fd);
		      $fwrite (fd, " 1049");
		   end
		 7'b00_?_110_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1050");
		      case ({foo[ 9],foo[ 5]})
			2'b00:
			  begin
			     $fwrite (fd, " 1051");
			     ozoneae(foo[14:12], fd);
			     ozonehl(foo[ 5], fd);
			  end
			2'b01:
			  begin
			     $fwrite (fd, " 1052");
			     ozoneae(foo[14:12], fd);
			     ozonehl(foo[ 5], fd);
			  end
			2'b10:
			  begin
			     $fwrite (fd, " 1053");
			     ozoneae(foo[14:12], fd);
			  end
			2'b11: $fwrite (fd, " 1054");
		      endcase
		      dude(fd);
		      $fwrite (fd, " 1055");
		   end
		 7'b01_?_110_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1056");
		      case ({foo[ 9],foo[ 5]})
			2'b00:
			  begin
			     ozoneae(foo[14:12], fd);
			     ozonehl(foo[ 5], fd);
			     $fwrite (fd, " 1057");
			  end
			2'b01:
			  begin
			     ozoneae(foo[14:12], fd);
			     ozonehl(foo[ 5], fd);
			     $fwrite (fd, " 1058");
			  end
			2'b10:
			  begin
			     ozoneae(foo[14:12], fd);
			     $fwrite (fd, " 1059");
			  end
			2'b11: $fwrite (fd, " 1060");
		      endcase
		      dude(fd);
		      $fwrite (fd, " 1061");
		   end
		 7'b10_0_110_0:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1062");
		      $fwrite (fd, " 1063");
		      if (foo[12])
			$fwrite (fd, " 1064");
		      else
			ozonerab({4'b1001, foo[14:12]}, fd);
		      dude(fd);
		      $fwrite (fd, " 1065");
		   end
		 7'b10_0_110_1:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1066");
		      if (foo[12])
			$fwrite (fd, " 1067");
		      else
			ozonerab({4'b1001, foo[14:12]}, fd);
		      $fwrite (fd, " 1068");
		      dude(fd);
		      $fwrite (fd, " 1069");
		   end
		 7'b??_?_000_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1070");
		      $fwrite (fd, " 1071");
		      ozonef1e_hl(foo[11:9],foo[ 5], fd);
		      $fwrite (fd, " 1072");
		      ozonef1e_ye(foo[14:9],foo[ 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1073");
		   end
		 7'b??_?_100_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1074");
		      $fwrite (fd, " 1075");
		      ozonef1e_hl(foo[11:9],foo[ 5], fd);
		      $fwrite (fd, " 1076");
		      ozonef1e_ye(foo[14:9],foo[ 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1077");
		   end
		 7'b??_?_001_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1078");
		      ozonef1e_ye(foo[14:9],foo[ 5], fd);
		      $fwrite (fd, " 1079");
		      $fwrite (fd, " 1080");
		      ozonef1e_hl(foo[11:9],foo[ 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1081");
		   end
		 7'b??_?_011_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1082");
		      ozonef1e_ye(foo[14:9],foo[ 5], fd);
		      $fwrite (fd, " 1083");
		      $fwrite (fd, " 1084");
		      ozonef1e_hl(foo[11:9],foo[ 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1085");
		   end
		 7'b??_?_101_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1086");
		      ozonef1e_ye(foo[14:9],foo[ 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1087");
		   end
               endcase
             17'b00_10??_?_????_?0_0110 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1088");
		  ozoneae(foo[ 8: 6], fd);
		  ozonef1e_hl(foo[11:9],foo[ 5], fd);
		  $fwrite (fd, " 1089");
		  ozonef1e_ye(foo[14:9],foo[ 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1090");
               end
             17'b00_10??_?_????_00_0111 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1091");
		  if (foo[ 6])
		    $fwrite (fd, " 1092");
		  else
		    ozonerab({4'b1001, foo[ 8: 6]}, fd);
		  $fwrite (fd, " 1093");
		  $fwrite (fd, " 1094");
		  ozonerme(foo[14:12], fd);
		  case (foo[11: 9])
		    3'h2,
		      3'h5,
		      3'h6,
		      3'h7:
			ozonef1e_inc_dec(foo[14:9],1'b0, fd);
		    3'h1,
		      3'h3,
		      3'h4:
			$fwrite (fd, " 1095");
		  endcase
		  dude(fd);
		  $fwrite (fd, " 1096");
               end
             17'b00_10??_?_????_?0_0100 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1097");
		  ozonef1e_ye(foo[14:9],foo[ 5], fd);
		  $fwrite (fd, " 1098");
		  ozoneae(foo[ 8: 6], fd);
		  ozonef1e_hl(foo[11:9],foo[ 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1099");
               end
             17'b00_10??_?_????_10_0111 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1100");
		  $fwrite (fd, " 1101");
		  ozonerme(foo[14:12], fd);
		  case (foo[11: 9])
		    3'h2,
		      3'h5,
		      3'h6,
		      3'h7:
			ozonef1e_inc_dec(foo[14:9],1'b0, fd);
		    3'h1,
		      3'h3,
		      3'h4:
			$fwrite (fd, " 1102");
		  endcase
		  $fwrite (fd, " 1103");
		  if (foo[ 6])
		    $fwrite (fd, " 1104");
		  else
		    ozonerab({4'b1001, foo[ 8: 6]}, fd);
		  dude(fd);
		  $fwrite (fd, " 1105");
               end
             17'b00_10??_?_????_?0_1110 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1106");
		  case (foo[11:9])
		    3'h2:
		      begin
			 $fwrite (fd, " 1107");
			 if (foo[14:12] == 3'h0)
			   $fwrite (fd, " 1108");
			 else
			   ozonerme(foo[14:12], fd);
			 $fwrite (fd, " 1109");
		      end
		    3'h6:
		      begin
			 $fwrite (fd, " 1110");
			 if (foo[14:12] == 3'h0)
			   $fwrite (fd, " 1111");
			 else
			   ozonerme(foo[14:12], fd);
			 $fwrite (fd, " 1112");
		      end
		    3'h0:
		      begin
			 $fwrite (fd, " 1113");
			 if (foo[14:12] == 3'h0)
			   $fwrite (fd, " 1114");
			 else
			   ozonerme(foo[14:12], fd);
			 $fwrite (fd, " 1115");
			 if (foo[ 7: 5] >= 3'h5)
			   $fwrite (fd, " 1116");
			 else
			   ozonexe(foo[ 8: 5], fd);
		      end
		    3'h1:
		      begin
			 $fwrite (fd, " 1117");
			 if (foo[14:12] == 3'h0)
			   $fwrite (fd, " 1118");
			 else
			   ozonerme(foo[14:12], fd);
			 $fwrite (fd, " 1119");
			 if (foo[ 7: 5] >= 3'h5)
			   $fwrite (fd, " 1120");
			 else
			   ozonexe(foo[ 8: 5], fd);
		      end
		    3'h4:
		      begin
			 $fwrite (fd, " 1121");
			 if (foo[14:12] == 3'h0)
			   $fwrite (fd, " 1122");
			 else
			   ozonerme(foo[14:12], fd);
			 $fwrite (fd, " 1123");
			 if (foo[ 7: 5] >= 3'h5)
			   $fwrite (fd, " 1124");
			 else
			   ozonexe(foo[ 8: 5], fd);
		      end
		    3'h5:
		      begin
			 $fwrite (fd, " 1125");
			 if (foo[14:12] == 3'h0)
			   $fwrite (fd, " 1126");
			 else
			   ozonerme(foo[14:12], fd);
			 $fwrite (fd, " 1127");
			 if (foo[ 7: 5] >= 3'h5)
			   $fwrite (fd, " 1128");
			 else
			   ozonexe(foo[ 8: 5], fd);
		      end
		  endcase
		  dude(fd);
		  $fwrite (fd, " 1129");
               end
             17'b00_10??_?_????_?0_1111 :
               casez (foo[14: 9])
		 6'b001_10_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1130");
		      $fwrite (fd, " 1131");
		      ozonef1e_hl(foo[ 7: 5],foo[ 9], fd);
		      $fwrite (fd, " 1132");
		      ozonexe(foo[ 8: 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1133");
		   end
		 6'b???_11_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1134");
		      ozoneae(foo[14:12], fd);
		      ozonef1e_hl(foo[ 7: 5],foo[ 9], fd);
		      $fwrite (fd, " 1135");
		      ozonexe(foo[ 8: 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1136");
		   end
		 6'b000_10_1,
		   6'b010_10_1,
		   6'b100_10_1,
		   6'b110_10_1:
		     begin
			ozonef1e(foo, fd);
			$fwrite (fd, " 1137");
			ozonerab({4'b1001, foo[14:12]}, fd);
			$fwrite (fd, " 1138");
			if ((foo[ 7: 5] >= 3'h1) & (foo[ 7: 5] <= 3'h3))
			  $fwrite (fd, " 1139");
			else
			  ozonexe(foo[ 8: 5], fd);
			dude(fd);
			$fwrite (fd, " 1140");
		     end
		 6'b000_10_0,
		   6'b010_10_0,
		   6'b100_10_0,
		   6'b110_10_0:
		     begin
			ozonef1e(foo, fd);
			$fwrite (fd, " 1141");
			$fwrite (fd, " 1142");
			ozonerab({4'b1001, foo[14:12]}, fd);
			$fwrite (fd, " 1143");
			$fwrite (fd, " 1144");
			ozonef1e_h(foo[ 7: 5], fd);
			$fwrite (fd, " 1145");
			ozonexe(foo[ 8: 5], fd);
			dude(fd);
			$fwrite (fd, " 1146");
		     end
		 6'b???_00_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1147");
		      if (foo[ 9])
			begin
			   $fwrite (fd, " 1148");
			   ozoneae(foo[14:12], fd);
			end
		      else
			begin
			   $fwrite (fd, " 1149");
			   ozoneae(foo[14:12], fd);
			   $fwrite (fd, " 1150");
			end
		      $fwrite (fd, " 1151");
		      $fwrite (fd, " 1152");
		      ozonef1e_h(foo[ 7: 5], fd);
		      $fwrite (fd, " 1153");
		      ozonexe(foo[ 8: 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1154");
		   end
		 6'b???_01_?:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1155");
		      ozoneae(foo[14:12], fd);
		      if (foo[ 9])
			$fwrite (fd, " 1156");
		      else
			$fwrite (fd, " 1157");
		      $fwrite (fd, " 1158");
		      $fwrite (fd, " 1159");
		      ozonef1e_h(foo[ 7: 5], fd);
		      $fwrite (fd, " 1160");
		      ozonexe(foo[ 8: 5], fd);
		      dude(fd);
		      $fwrite (fd, " 1161");
		   end
		 6'b011_10_0:
		   begin
		      ozonef1e(foo, fd);
		      $fwrite (fd, " 1162");
		      case (foo[ 8: 5])
			4'h0:  $fwrite (fd, " 1163");
			4'h1:  $fwrite (fd, " 1164");
			4'h2:  $fwrite (fd, " 1165");
			4'h3:  $fwrite (fd, " 1166");
			4'h4:  $fwrite (fd, " 1167");
			4'h5:  $fwrite (fd, " 1168");
			4'h8:  $fwrite (fd, " 1169");
			4'h9:  $fwrite (fd, " 1170");
			4'ha:  $fwrite (fd, " 1171");
			4'hb:  $fwrite (fd, " 1172");
			4'hc:  $fwrite (fd, " 1173");
			4'hd:  $fwrite (fd, " 1174");
			default: $fwrite (fd, " 1175");
		      endcase
		      dude(fd);
		      $fwrite (fd, " 1176");
		   end
		 default: $fwrite (fd, " 1177");
               endcase
             17'b00_10??_?_????_?0_110? :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1178");
		  $fwrite (fd, " 1179");
		  ozonef1e_hl(foo[11:9], foo[0], fd);
		  $fwrite (fd, " 1180");
		  ozonef1e_ye(foo[14:9],1'b0, fd);
		  $fwrite (fd, " 1181");
		  ozonef1e_h(foo[ 7: 5], fd);
		  $fwrite (fd, " 1182");
		  ozonexe(foo[ 8: 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1183");
               end
             17'b00_10??_?_????_?1_110? :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1184");
		  $fwrite (fd, " 1185");
		  ozonef1e_hl(foo[11:9],foo[0], fd);
		  $fwrite (fd, " 1186");
		  ozonef1e_ye(foo[14:9],foo[ 0], fd);
		  $fwrite (fd, " 1187");
		  $fwrite (fd, " 1188");
		  ozonef1e_h(foo[ 7: 5], fd);
		  $fwrite (fd, " 1189");
		  ozonexe(foo[ 8: 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1190");
               end
             17'b00_10??_?_????_?0_101? :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1191");
		  ozonef1e_ye(foo[14:9],foo[ 0], fd);
		  $fwrite (fd, " 1192");
		  $fwrite (fd, " 1193");
		  ozonef1e_hl(foo[11:9],foo[0], fd);
		  $fwrite (fd, " 1194");
		  $fwrite (fd, " 1195");
		  ozonef1e_h(foo[ 7: 5], fd);
		  $fwrite (fd, " 1196");
		  ozonexe(foo[ 8: 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1197");
               end
             17'b00_10??_?_????_?0_1001 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1198");
		  $fwrite (fd, " 1199");
		  ozonef1e_h(foo[11:9], fd);
		  $fwrite (fd, " 1200");
		  ozonef1e_ye(foo[14:9],1'b0, fd);
		  $fwrite (fd, " 1201");
		  case (foo[ 7: 5])
		    3'h1,
		      3'h2,
		      3'h3:
			$fwrite (fd, " 1202");
		    default:
		      begin
			 $fwrite (fd, " 1203");
			 $fwrite (fd, " 1204");
			 ozonexe(foo[ 8: 5], fd);
		      end
		  endcase
		  dude(fd);
		  $fwrite (fd, " 1205");
               end
             17'b00_10??_?_????_?0_0101 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1206");
		  case (foo[11: 9])
		    3'h1,
		      3'h3,
		      3'h4:
			$fwrite (fd, " 1207");
		    default:
		      begin
			 ozonef1e_ye(foo[14:9],1'b0, fd);
			 $fwrite (fd, " 1208");
			 $fwrite (fd, " 1209");
		      end
		  endcase
		  $fwrite (fd, " 1210");
		  $fwrite (fd, " 1211");
		  ozonef1e_h(foo[ 7: 5], fd);
		  $fwrite (fd, " 1212");
		  ozonexe(foo[ 8: 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1213");
               end
             17'b00_10??_?_????_?1_1110 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1214");
		  ozonef1e_ye(foo[14:9],1'b0, fd);
		  $fwrite (fd, " 1215");
		  $fwrite (fd, " 1216");
		  ozonef1e_h(foo[11: 9], fd);
		  $fwrite (fd, " 1217");
		  $fwrite (fd, " 1218");
		  ozonef1e_h(foo[ 7: 5], fd);
		  $fwrite (fd, " 1219");
		  ozonexe(foo[ 8: 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1220");
               end
             17'b00_10??_?_????_?0_1000 :
               begin
		  ozonef1e(foo, fd);
		  $fwrite (fd, " 1221");
		  ozonef1e_ye(foo[14:9],1'b0, fd);
		  $fwrite (fd, " 1222");
		  $fwrite (fd, " 1223");
		  ozonef1e_h(foo[11: 9], fd);
		  $fwrite (fd, " 1224");
		  $fwrite (fd, " 1225");
		  ozonef1e_h(foo[ 7: 5], fd);
		  $fwrite (fd, " 1226");
		  ozonexe(foo[ 8: 5], fd);
		  dude(fd);
		  $fwrite (fd, " 1227");
               end
             17'b10_01??_?_????_??_???? :
               begin
		  if (foo[27])
		    $fwrite (fd," 1228");
		  else
		    $fwrite (fd," 1229");
		  ozonecon(foo[20:16], fd);
		  $fwrite (fd, " 1230");
		  ozonef2(foo[31:0], fd);
		  dude(fd);
		  $fwrite (fd, " 1231");
               end
             17'b00_1000_?_????_01_0011 :
               if (~|foo[ 9: 8])
		 begin
		    if (foo[ 7])
		      $fwrite (fd," 1232");
		    else
		      $fwrite (fd," 1233");
		    ozonecon(foo[14:10], fd);
		    $fwrite (fd, " 1234");
		    ozonef2e(foo[31:0], fd);
		    dude(fd);
		    $fwrite (fd, " 1235");
		 end
               else
		 begin
		    $fwrite (fd, " 1236");
		    ozonecon(foo[14:10], fd);
		    $fwrite (fd, " 1237");
		    ozonef3e(foo[31:0], fd);
		    dude(fd);
		    $fwrite (fd, " 1238");
		 end
             17'b11_110?_1_????_??_???? :
               begin
		  ozonef3(foo[31:0], fd);
		  dude(fd);
		  $fwrite(fd, " 1239");
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
			 ozoneacc(foo[26], fd);
			 $fwrite (fd, " 1241");
			 ozoneacc(foo[25], fd);
			 ozonebmuop(foo[24:20], fd);
			 ozoneae(foo[18:16], fd);
			 $fwrite (fd, " 1242");
			 dude(fd);
			 $fwrite(fd, " 1243");
		      end
		    5'b0_01??:
		      begin
			 ozoneacc(foo[26], fd);
			 $fwrite (fd, " 1244");
			 ozoneacc(foo[25], fd);
			 ozonebmuop(foo[24:20], fd);
			 ozonearm(foo[18:16], fd);
			 dude(fd);
			 $fwrite(fd, " 1245");
		      end
		    5'b0_1011:
		      begin
			 ozoneacc(foo[26], fd);
			 $fwrite (fd, " 1246");
			 ozonebmuop(foo[24:20], fd);
			 $fwrite (fd, " 1247");
			 ozoneae(foo[18:16], fd);
			 $fwrite (fd, " 1248");
			 dude(fd);
			 $fwrite(fd, " 1249");
		      end
		    5'b0_100?,
		      5'b0_1010,
		      5'b0_110? :
			begin
			   ozoneacc(foo[26], fd);
			   $fwrite (fd, " 1250");
			   ozonebmuop(foo[24:20], fd);
			   $fwrite (fd, " 1251");
			   ozoneacc(foo[25], fd);
			   $fwrite (fd, " 1252");
			   ozoneae(foo[18:16], fd);
			   $fwrite (fd, " 1253");
			   dude(fd);
			   $fwrite(fd, " 1254");
			end
		    5'b0_1111 :
		      begin
			 ozoneacc(foo[26], fd);
			 $fwrite (fd, " 1255");
			 ozoneacc(foo[25], fd);
			 $fwrite (fd, " 1256");
			 ozoneae(foo[18:16], fd);
			 dude(fd);
			 $fwrite(fd, " 1257");
		      end
		    5'b1_10??,
		      5'b1_110?,
		      5'b1_1110 :
			begin
			   ozoneacc(foo[26], fd);
			   $fwrite (fd, " 1258");
			   ozonebmuop(foo[24:20], fd);
			   $fwrite (fd, " 1259");
			   ozoneacc(foo[25], fd);
			   $fwrite (fd, " 1260");
			   ozonearm(foo[18:16], fd);
			   $fwrite (fd, " 1261");
			   dude(fd);
			   $fwrite(fd, " 1262");
			end
		  endcase
               end
             17'b11_100?_?_????_??_???? :
               casez (foo[23:19])
		 5'b111??,
		   5'b0111?:
		     begin
			ozoneae(foo[26:24], fd);
			$fwrite (fd, " 1263");
			ozonef3f4imop(foo[23:19], fd);
			$fwrite (fd, " 1264");
			ozoneae(foo[18:16], fd);
			$fwrite (fd, " 1265");
			skyway(foo[15:12], fd);
			skyway(foo[11: 8], fd);
			skyway(foo[ 7: 4], fd);
			skyway(foo[ 3:0], fd);
			$fwrite (fd, " 1266");
			dude(fd);
			$fwrite(fd, " 1267");
		     end
		 5'b?0???,
		   5'b110??:
		     begin
			ozoneae(foo[26:24], fd);
			$fwrite (fd, " 1268");
			if (foo[23:21] == 3'b100)
			  $fwrite (fd, " 1269");
			ozoneae(foo[18:16], fd);
			if (foo[19])
			  $fwrite (fd, " 1270");
			else
			  $fwrite (fd, " 1271");
			ozonef3f4imop(foo[23:19], fd);
			$fwrite (fd, " 1272");
			ozonef3f4_iext(foo[20:19], foo[15:0], fd);
			dude(fd);
			$fwrite(fd, " 1273");
		     end
		 5'b010??,
		   5'b0110?:
		     begin
			ozoneae(foo[18:16], fd);
			if (foo[19])
			  $fwrite (fd, " 1274");
			else
			  $fwrite (fd, " 1275");
			ozonef3f4imop(foo[23:19], fd);
			$fwrite (fd, " 1276");
			ozonef3f4_iext(foo[20:19], foo[15:0], fd);
			dude(fd);
			$fwrite(fd, " 1277");
		     end
               endcase
             17'b00_1000_?_????_11_0011 :
               begin
		  $fwrite (fd," 1278");
		  ozonecon(foo[14:10], fd);
		  $fwrite (fd, " 1279");
		  casez (foo[25:21])
		    5'b0_1110,
		      5'b1_0???,
		      5'b1_1111:
			begin
			   $fwrite(fd, " 1280");
			end
		    5'b0_00??:
		      begin
			 ozoneae(foo[20:18], fd);
			 $fwrite (fd, " 1281");
			 ozoneae(foo[17:15], fd);
			 ozonebmuop(foo[25:21], fd);
			 ozoneae(foo[ 8: 6], fd);
			 $fwrite (fd, " 1282");
			 dude(fd);
			 $fwrite(fd, " 1283");
		      end
		    5'b0_01??:
		      begin
			 ozoneae(foo[20:18], fd);
			 $fwrite (fd, " 1284");
			 ozoneae(foo[17:15], fd);
			 ozonebmuop(foo[25:21], fd);
			 ozonearm(foo[ 8: 6], fd);
			 dude(fd);
			 $fwrite(fd, " 1285");
		      end
		    5'b0_1011:
		      begin
			 ozoneae(foo[20:18], fd);
			 $fwrite (fd, " 1286");
			 ozonebmuop(foo[25:21], fd);
			 $fwrite (fd, " 1287");
			 ozoneae(foo[ 8: 6], fd);
			 $fwrite (fd, " 1288");
			 dude(fd);
			 $fwrite(fd, " 1289");
		      end
		    5'b0_100?,
		      5'b0_1010,
		      5'b0_110? :
			begin
			   ozoneae(foo[20:18], fd);
			   $fwrite (fd, " 1290");
			   ozonebmuop(foo[25:21], fd);
			   $fwrite (fd, " 1291");
			   ozoneae(foo[17:15], fd);
			   $fwrite (fd, " 1292");
			   ozoneae(foo[ 8: 6], fd);
			   $fwrite (fd, " 1293");
			   dude(fd);
			   $fwrite(fd, " 1294");
			end
		    5'b0_1111 :
		      begin
			 ozoneae(foo[20:18], fd);
			 $fwrite (fd, " 1295");
			 ozoneae(foo[17:15], fd);
			 $fwrite (fd, " 1296");
			 ozoneae(foo[ 8: 6], fd);
			 dude(fd);
			 $fwrite(fd, " 1297");
		      end
		    5'b1_10??,
		      5'b1_110?,
		      5'b1_1110 :
			begin
			   ozoneae(foo[20:18], fd);
			   $fwrite (fd, " 1298");
			   ozonebmuop(foo[25:21], fd);
			   $fwrite (fd, " 1299");
			   ozoneae(foo[17:15], fd);
			   $fwrite (fd, " 1300");
			   ozonearm(foo[ 8: 6], fd);
			   $fwrite (fd, " 1301");
			   dude(fd);
			   $fwrite(fd, " 1302");
			end
		  endcase
               end
             17'b00_0010_?_????_??_???? :
               begin
		  ozonerab({1'b0, foo[25:20]}, fd);
		  $fwrite (fd, " 1303");
		  skyway(foo[19:16], fd);
		  dude(fd);
		  $fwrite(fd, " 1304");
               end
             17'b00_01??_?_????_??_???? :
               begin
		  if (foo[27])
		    begin
		       $fwrite (fd, " 1305");
		       if (foo[26])
			 $fwrite (fd, " 1306");
		       else
			 $fwrite (fd, " 1307");
		       skyway(foo[19:16], fd);
		       $fwrite (fd, " 1308");
		       ozonerab({1'b0, foo[25:20]}, fd);
		    end
		  else
		    begin
		       ozonerab({1'b0, foo[25:20]}, fd);
		       $fwrite (fd, " 1309");
		       if (foo[26])
			 $fwrite (fd, " 1310");
		       else
			 $fwrite (fd, " 1311");
		       skyway(foo[19:16], fd);
		       $fwrite (fd, " 1312");
		    end
		  dude(fd);
		  $fwrite(fd, " 1313");
               end
             17'b01_000?_?_????_??_???? :
               begin
		  if (foo[26])
		    begin
		       ozonerb(foo[25:20], fd);
		       $fwrite (fd, " 1314");
		       ozoneae(foo[18:16], fd);
		       ozonehl(foo[19], fd);
		    end
		  else
		    begin
		       ozoneae(foo[18:16], fd);
		       ozonehl(foo[19], fd);
		       $fwrite (fd, " 1315");
		       ozonerb(foo[25:20], fd);
		    end
		  dude(fd);
		  $fwrite(fd, " 1316");
               end
             17'b01_10??_?_????_??_???? :
               begin
		  if (foo[27])
		    begin
		       ozonerab({1'b0, foo[25:20]}, fd);
		       $fwrite (fd, " 1317");
		       ozonerx(foo, fd);
		    end
		  else
		    begin
		       ozonerx(foo, fd);
		       $fwrite (fd, " 1318");
		       ozonerab({1'b0, foo[25:20]}, fd);
		    end
		  dude(fd);
		  $fwrite(fd, " 1319");
               end
             17'b11_101?_?_????_??_???? :
               begin
		  ozonerab (foo[26:20], fd);
		  $fwrite (fd, " 1320");
		  skyway(foo[19:16], fd);
		  skyway(foo[15:12], fd);
		  skyway(foo[11: 8], fd);
		  skyway(foo[ 7: 4], fd);
		  skyway(foo[ 3: 0], fd);
		  dude(fd);
		  $fwrite(fd, " 1321");
               end
             17'b11_0000_?_????_??_???? :
               begin
		  casez (foo[25:23])
		    3'b00?:
		      begin
			 ozonerab(foo[22:16], fd);
			 $fwrite (fd, " 1322");
		      end
		    3'b01?:
		      begin
			 $fwrite (fd, " 1323");
			 if (foo[22:16]>=7'h60)
			   $fwrite (fd, " 1324");
			 else
			   ozonerab(foo[22:16], fd);
		      end
		    3'b110:
		      $fwrite (fd, " 1325");
		    3'b10?:
		      begin
			 $fwrite (fd, " 1326");
			 if (foo[22:16]>=7'h60)
			   $fwrite (fd, " 1327");
			 else
			   ozonerab(foo[22:16], fd);
		      end
		    3'b111:
		      begin
			 $fwrite (fd, " 1328");
			 ozonerab(foo[22:16], fd);
			 $fwrite (fd, " 1329");
		      end
		  endcase
		  dude(fd);
		  $fwrite(fd, " 1330");
               end
             17'b00_10??_?_????_?1_0000 :
               begin
		  if (foo[27])
		    begin
		       $fwrite (fd, " 1331");
		       ozonerp(foo[14:12], fd);
		       $fwrite (fd, " 1332");
		       skyway(foo[19:16], fd);
		       skyway({foo[15],foo[11: 9]}, fd);
		       skyway(foo[ 8: 5], fd);
		       $fwrite (fd, " 1333");
		       if (foo[26:20]>=7'h60)
			 $fwrite (fd, " 1334");
		       else
			 ozonerab(foo[26:20], fd);
		    end
		  else
		    begin
		       ozonerab(foo[26:20], fd);
		       $fwrite (fd, " 1335");
		       $fwrite (fd, " 1336");
		       ozonerp(foo[14:12], fd);
		       $fwrite (fd, " 1337");
		       skyway(foo[19:16], fd);
		       skyway({foo[15],foo[11: 9]}, fd);
		       skyway(foo[ 8: 5], fd);
		       $fwrite (fd, " 1338");
		    end
		  dude(fd);
		  $fwrite(fd, " 1339");
               end
             17'b00_101?_1_0000_?1_0010 :
               if (~|foo[11: 7])
		 begin
		    if (foo[ 6])
		      begin
			 $fwrite (fd, " 1340");
			 ozonerp(foo[14:12], fd);
			 $fwrite (fd, " 1341");
			 ozonejk(foo[ 5], fd);
			 $fwrite (fd, " 1342");
			 if (foo[26:20]>=7'h60)
			   $fwrite (fd, " 1343");
			 else
			   ozonerab(foo[26:20], fd);
		      end
		    else
		      begin
			 ozonerab(foo[26:20], fd);
			 $fwrite (fd, " 1344");
			 $fwrite (fd, " 1345");
			 ozonerp(foo[14:12], fd);
			 $fwrite (fd, " 1346");
			 ozonejk(foo[ 5], fd);
			 $fwrite (fd, " 1347");
		      end
		    dude(fd);
		    $fwrite(fd, " 1348");
		 end
               else
		 $fwrite(fd, " 1349");
             17'b00_100?_0_0011_?1_0101 :
               if (~|foo[ 8: 7])
		 begin
		    if (foo[6])
		      begin
			 ozonerab(foo[26:20], fd);
			 $fwrite (fd, " 1350");
			 ozoneye(foo[14: 9],foo[ 5], fd);
		      end
		    else
		      begin
			 ozoneye(foo[14: 9],foo[ 5], fd);
			 $fwrite (fd, " 1351");
			 if (foo[26:20]>=7'h60)
			   $fwrite (fd, " 1352");
			 else
			   ozonerab(foo[26:20], fd);
		      end
		    dude(fd);
		    $fwrite(fd, " 1353");
		 end
               else
		 $fwrite(fd, " 1354");
             17'b00_1001_0_0000_?1_0010 :
               if (~|foo[25:20])
		 begin
		    ozoneye(foo[14: 9],1'b0, fd);
		    $fwrite (fd, " 1355");
		    ozonef1e_h(foo[11: 9], fd);
		    $fwrite (fd, " 1356");
		    ozonef1e_h(foo[ 7: 5], fd);
		    $fwrite (fd, " 1357");
		    ozonexe(foo[ 8: 5], fd);
		    dude(fd);
		    $fwrite(fd, " 1358");
		 end
               else
		 $fwrite(fd, " 1359");
             17'b00_101?_0_????_?1_0010 :
               if (~foo[13])
		 begin
		    if (foo[12])
		      begin
			 $fwrite (fd, " 1360");
			 if (foo[26:20]>=7'h60)
			   $fwrite (fd, " 1361");
			 else
			   ozonerab(foo[26:20], fd);
			 $fwrite (fd, " 1362");
			 $fwrite (fd, " 1363");
			 skyway({1'b0,foo[18:16]}, fd);
			 skyway({foo[15],foo[11: 9]}, fd);
			 skyway(foo[ 8: 5], fd);
			 dude(fd);
			 $fwrite(fd, " 1364");
		      end
		    else
		      begin
			 ozonerab(foo[26:20], fd);
			 $fwrite (fd, " 1365");
			 $fwrite (fd, " 1366");
			 skyway({1'b0,foo[18:16]}, fd);
			 skyway({foo[15],foo[11: 9]}, fd);
			 skyway(foo[ 8: 5], fd);
			 dude(fd);
			 $fwrite(fd, " 1367");
		      end
		 end
               else
		 $fwrite(fd, " 1368");
             17'b01_01??_?_????_??_???? :
               begin
		  ozonerab({1'b0,foo[27:26],foo[19:16]}, fd);
		  $fwrite (fd, " 1369");
		  ozonerab({1'b0,foo[25:20]}, fd);
		  dude(fd);
		  $fwrite(fd, " 1370");
               end
             17'b00_100?_?_???0_11_0101 :
               if (~foo[6])
		 begin
		    $fwrite (fd," 1371");
		    ozonecon(foo[14:10], fd);
		    $fwrite (fd, " 1372");
		    ozonerab({foo[ 9: 7],foo[19:16]}, fd);
		    $fwrite (fd, " 1373");
		    ozonerab({foo[26:20]}, fd);
		    dude(fd);
		    $fwrite(fd, " 1374");
		 end
               else
		 $fwrite(fd, " 1375");
             17'b00_1000_?_????_?1_0010 :
               if (~|foo[25:24])
		 begin
		    ozonery(foo[23:20], fd);
		    $fwrite (fd, " 1376");
		    ozonerp(foo[14:12], fd);
		    $fwrite (fd, " 1377");
		    skyway(foo[19:16], fd);
		    skyway({foo[15],foo[11: 9]}, fd);
		    skyway(foo[ 8: 5], fd);
		    dude(fd);
		    $fwrite(fd, " 1378");
		 end
               else if ((foo[25:24] == 2'b10) & ~|foo[19:15] & ~|foo[11: 6])
		 begin
		    ozonery(foo[23:20], fd);
		    $fwrite (fd, " 1379");
		    ozonerp(foo[14:12], fd);
		    $fwrite (fd, " 1380");
		    ozonejk(foo[ 5], fd);
		    dude(fd);
		    $fwrite(fd, " 1381");
		 end
               else
		 $fwrite(fd, " 1382");
             17'b11_01??_?_????_??_????,
               17'b10_00??_?_????_??_???? :
		 if (foo[30])
		   $fwrite(fd, " 1383:%x", foo[27:16]);
		 else
		   $fwrite(fd, " 1384:%x", foo[27:16]);
             17'b00_10??_?_????_01_1000 :
               if (~foo[6])
		 begin
		    if (foo[7])
		      $fwrite(fd, " 1385:%x", foo[27: 8]);
		    else
		      $fwrite(fd, " 1386:%x", foo[27: 8]);
		 end
               else
		 $fwrite(fd, " 1387");
             17'b00_10??_?_????_11_1000 :
               begin
		  $fwrite (fd," 1388");
		  ozonecon(foo[14:10], fd);
		  $fwrite (fd, " 1389");
		  if (foo[15])
		    $fwrite (fd, " 1390");
		  else
		    $fwrite (fd, " 1391");
		  skyway(foo[27:24], fd);
		  skyway(foo[23:20], fd);
		  skyway(foo[19:16], fd);
		  skyway(foo[ 9: 6], fd);
		  dude(fd);
		  $fwrite(fd, " 1392");
               end
             17'b11_0001_?_????_??_???? :
               casez (foo[25:22])
		 4'b01?? :
		   begin
		      $fwrite (fd," 1393");
		      ozonecon(foo[20:16], fd);
		      case (foo[23:21])
			3'h0 :  $fwrite (fd, " 1394");
			3'h1 :  $fwrite (fd, " 1395");
			3'h2 :  $fwrite (fd, " 1396");
			3'h3 :  $fwrite (fd, " 1397");
			3'h4 :  $fwrite (fd, " 1398");
			3'h5 :  $fwrite (fd, " 1399");
			3'h6 :  $fwrite (fd, " 1400");
			3'h7 :  $fwrite (fd, " 1401");
		      endcase
		      dude(fd);
		      $fwrite(fd, " 1402");
		   end
		 4'b0000 :
		   $fwrite(fd, " 1403:%x", foo[21:16]);
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
		 $fwrite(fd, " 1408:%x", foo[22:16]);
               else
		 $fwrite(fd, " 1409:%x", foo[22:16]);
             default: $fwrite(fd, " 1410");
	   endcase
      end
   endtask

   //(query-replace-regexp "\\([a-z0-9_]+\\) *( *\\([][a-z0-9_~': ]+\\) *, *\\([][a-z0-9'~: ]+\\) *, *\\([][a-z0-9'~: ]+\\) *);" "$c(\"\\1(\",\\2,\",\",\\3,\",\",\\4,\");\");" nil nil nil)
   //(query-replace-regexp "\\([a-z0-9_]+\\) *( *\\([][a-z0-9_~': ]+\\) *, *\\([][a-z0-9'~: ]+\\) *);" "$c(\"\\1(\",\\2,\",\",\\3,\");\");" nil nil nil)

endmodule
