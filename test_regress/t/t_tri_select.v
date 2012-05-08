// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks

`define WIDTH 2

module top (
    input OE1,
    input OE2,
    input [`WIDTH-1:0] A1,
    input [`WIDTH-1:0] A2,
    output [`WIDTH-1:0] Y1,
    output [`WIDTH-1:0] Y2,
    output [`WIDTH-1:0] Y3,
    output [`WIDTH**2-1:0] W);

   assign W[A1] = (OE2) ? A2[0] : 1'bz;
   assign W[A2] = (OE1) ? A2[1] : 1'bz;

   // have 2 different 'chips' drive the PAD to act like a bi-directional bus
   wire [`WIDTH-1:0] PAD;
   io_ring io_ring1 (.OE(OE1), .A(A1), .O(Y1), .PAD(PAD));
   io_ring io_ring2 (.OE(OE2), .A(A2), .O(Y2), .PAD(PAD));

   assign Y3 = PAD;

   pullup   p1(PAD);
//   pulldown  p1(PAD);


   wire [5:0] 	     fill = { 4'b0, A1 };

endmodule

module io_ring (input OE, input [`WIDTH-1:0] A, output [`WIDTH-1:0] O, inout [`WIDTH-1:0] PAD);
   io io[`WIDTH-1:0] (.OE(OE), .I(A), .O(O), .PAD(PAD));
endmodule

module io (input OE, input I, output O, inout PAD);
   assign O = PAD;
   assign PAD = OE ? I : 1'bz;
endmodule
