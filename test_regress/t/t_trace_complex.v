// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

bit global_bit;

module t (clk);
   input clk;
   integer 	cyc=0;

   typedef struct packed {
      bit	b1;
      bit	b0;
   } strp_t;

   typedef struct packed {
      strp_t	x1;
      strp_t	x0;
   } strp_strp_t;

   typedef union packed {
      strp_t	x1;
      strp_t	x0;
   } unip_strp_t;

   typedef bit [2:1] arrp_t;
   typedef arrp_t [4:3] arrp_arrp_t;

   typedef strp_t [4:3] arrp_strp_t;

   typedef bit arru_t [2:1];
   typedef arru_t arru_arru_t [4:3];
   typedef arrp_t arru_arrp_t [4:3];
   typedef strp_t arru_strp_t [4:3];

   strp_t 	v_strp;
   strp_strp_t	v_strp_strp;
   unip_strp_t	v_unip_strp;
   arrp_t	v_arrp;
   arrp_arrp_t	v_arrp_arrp;
   arrp_strp_t	v_arrp_strp;
   arru_t	v_arru;
   arru_arru_t	v_arru_arru;
   arru_arrp_t	v_arru_arrp;
   arru_strp_t	v_arru_strp;

   real         v_real;
   real         v_arr_real [2];
   string	v_string;

   string       v_assoc[string];
   initial v_assoc["key"] = "value";

   typedef struct packed {
      logic [31:0] data;
   } str32_t;
   str32_t [1:0] v_str32x2;  // If no --trace-struct, this packed array is traced as 63:0
   initial v_str32x2[0] = 32'hff;
   initial v_str32x2[1] = 0;

   typedef enum int { ZERO=0, ONE, TWO, THREE } enumed_t;
   enumed_t v_enumed;
   enumed_t v_enumed2;
   typedef enum logic [2:0] { BZERO=0, BONE, BTWO, BTHREE } enumb_t;
   enumb_t v_enumb;
   typedef struct packed {
      enumb_t a;
      enumb_t b;
   } enumb2_str_t;
   enumb2_str_t v_enumb2_str;

   logic [7:0] unpacked_array[-2:0];

   p #(.PARAM(2)) p2 ();
   p #(.PARAM(3)) p3 ();

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      v_strp <= ~v_strp;
      v_strp_strp <= ~v_strp_strp;
      v_unip_strp <= ~v_unip_strp;
      v_arrp_strp <= ~v_arrp_strp;
      v_arrp <= ~v_arrp;
      v_arrp_arrp <= ~v_arrp_arrp;
      v_real <= v_real + 0.1;
      v_string <= cyc[0] ? "foo" : "bar";
      v_arr_real[0] <= v_arr_real[0] + 0.2;
      v_arr_real[1] <= v_arr_real[1] + 0.3;
      v_enumed <= v_enumed + 1;
      v_enumed2 <= v_enumed2 + 2;
      v_enumb <= v_enumb - 1;
      v_enumb2_str <= {v_enumb, v_enumb};
      for (integer b=3; b<=4; b++) begin
	 v_arru[b] <= ~v_arru[b];
	 v_arru_strp[b] <= ~v_arru_strp[b];
	 v_arru_arrp[b] <= ~v_arru_arrp[b];
	 for (integer a=3; a<=4; a++) begin
	    v_arru_arru[a][b] = ~v_arru_arru[a][b];
	 end
      end
      v_str32x2[0] <= v_str32x2[0] - 1;
      v_str32x2[1] <= v_str32x2[1] + 1;
      if (cyc == 5) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module p;
   parameter PARAM = 1;
   initial global_bit = 1;
endmodule
