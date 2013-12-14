// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

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

   typedef bit [2:1] arrp_t;
   typedef arrp_t [4:3] arrp_arrp_t;

   typedef strp_t [4:3] arrp_strp_t;

   typedef bit arru_t [2:1];
   typedef arru_t arru_arru_t [4:3];
   typedef arrp_t arru_arrp_t [4:3];
   typedef strp_t arru_strp_t [4:3];

   strp_t 	v_strp;
   strp_strp_t	v_strp_strp;
   arrp_t	v_arrp;
   arrp_arrp_t	v_arrp_arrp;
   arrp_strp_t	v_arrp_strp;
   arru_t	v_arru;
   arru_arru_t	v_arru_arru;
   arru_arrp_t	v_arru_arrp;
   arru_strp_t	v_arru_strp;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      v_strp <= ~v_strp;
      v_strp_strp <= ~v_strp_strp;
      v_arrp_strp <= ~v_arrp_strp;
      v_arrp <= ~v_arrp;
      v_arrp_arrp <= ~v_arrp_arrp;
      for (integer b=3; b<=4; b++) begin
	 v_arru[b] <= ~v_arru[b];
	 v_arru_strp[b] <= ~v_arru_strp[b];
	 v_arru_arrp[b] <= ~v_arru_arrp[b];
	 for (integer a=3; a<=4; a++) begin
	    v_arru_arru[a][b] = ~v_arru_arru[a][b];
	 end
      end
      if (cyc == 5) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
