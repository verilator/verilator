// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks

module top (input SEL, input[1:0] A, output W, output X, output Y, output Z);
   mux  mux2 (.A(A), .SEL(SEL), .Z(W));

   pass mux1 (.A(A), .SEL(SEL), .Z(X));

   tbuf mux0[1:0] (.A(A), .OE({SEL,!SEL}), .Z(Y));

   assign Z = ( SEL) ? A[1] : 1'bz;
   tbuf tbuf (.A(A[0]), .OE(!SEL), .Z(Z));
endmodule

module pass (input[1:0] A, input SEL, output Z);
   tbuf tbuf1 (.A(A[1]), .OE(SEL), .Z(Z));
   tbuf tbuf0 (.A(A[0]), .OE(!SEL),.Z(Z));
endmodule

module tbuf (input A, input OE, output Z);
`ifdef T_BUFIF0
   bufif0 (Z, A, !OE);
`elsif T_BUFIF1
   bufif1 (Z, A, OE);
`elsif T_NOTIF0
   notif0 (Z, !A, !OE);
`elsif T_NOTIF1
   notif1 (Z, !A, OE);
`elsif T_PMOS
   pmos (Z, A, !OE);
`elsif T_NMOS
   nmos (Z, A, OE);
`elsif T_COND
   assign Z = (OE) ? A : 1'bz;
`else
 `error "Unknown test name"
`endif
endmodule

module mux (input[1:0] A, input SEL, output Z);
   assign Z = (SEL) ? A[1] : 1'bz;
   assign Z = (!SEL)? A[0] : 1'bz;
   assign Z = 1'bz;
endmodule
