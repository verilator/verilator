// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

module top (input A, input B, input SEL, input clk, output Y1, output Y2, output Z, output done);
   io   io1(.A(A), .OE( SEL), .Z(Z), .Y(Y1));
   pass io2(.A(B), .OE(!SEL), .Z(Z), .Y(Y2));
   assign Z = 1'bz;

   pad_checker u_pad_checker(.clk(clk), .done(done));
endmodule

module pass (input A, input OE, inout Z, output Y);
   io_noinline io(.A(A), .OE(OE), .Z(Z), .Y(Y));
   assign Z = 1'bz;
endmodule

module io (input A, input OE, inout Z, output Y);
   assign Z = (OE) ? A : 1'bz;
   assign Y = Z;
   assign Z = 1'bz;
endmodule

module io_noinline (input A, input OE, inout Z, output Y);
   /*verilator no_inline_module*/
   assign Z = (OE) ? A : 1'bz;
   assign Y = Z;
   assign Z = 1'bz;
endmodule


module pad_checker(input wire clk, output wire done);
   wire tri_pad;
   reg [1:0] ie = '0;
   reg [1:0] oe = '0;
   reg [1:0] in = '0;
   wire out_0, out_1;

   pad u_pad0(.pad(tri_pad), .ie(ie[0]), .oe(oe[0]), .to_pad(in[0]), .from_pad(out_0));
   pad u_pad1(.pad(tri_pad), .ie(ie[1]), .oe(oe[1]), .to_pad(in[1]), .from_pad(out_1));

   wire bin_pad_in_0, bin_pad_in_1;
   wire bin_pad_01, bin_pad_10;
   wire bin_pad_en_01, bin_pad_en_10;
   wire bin_from_pad_out_0, bin_from_pad_out_1;
   wire bin_from_pad_en_0, bin_from_pad_en_1;

   // Expectation model that simulates how Verilator solves tri-state
   pad_binary u_pad_bin_0(.pad_in(bin_pad_in_0),
                          .pad_out(bin_pad_01),
                          .pad_en(bin_pad_en_01),
                          .ie(ie[0]), .oe(oe[0]),
                          .to_pad(in[0]),
                          .from_pad_out(bin_from_pad_out_0),
                          .from_pad_en(bin_from_pad_en_0));

   pad_binary u_pad_bin_1(.pad_in(bin_pad_in_1),
                          .pad_out(bin_pad_10),
                          .pad_en(bin_pad_en_10),
                          .ie(ie[1]),
                          .oe(oe[1]),
                          .to_pad(in[1]),
                          .from_pad_out(bin_from_pad_out_1),
                          .from_pad_en(bin_from_pad_en_1));

   assign bin_pad_in_0 = (bin_pad_en_10 & bin_pad_10) | (bin_pad_en_01 & bin_pad_01);
   assign bin_pad_in_1 = (bin_pad_en_01 & bin_pad_01) | (bin_pad_en_10 & bin_pad_10);


   logic done_reg = 0;
   assign done = done_reg;
   always @(posedge clk) begin
      if ({ie, oe, in} == 6'b111111) begin
         done_reg <= 1'b1;
     end else begin
         if (out_0 != bin_from_pad_out_0) begin
            $display("ie:%b oe:%b in:%b out0 act:%b exp:%b", ie[0], oe[0], in[0], out_0, bin_from_pad_out_0);
            $stop;
         end
         if (out_1 != bin_from_pad_out_1) begin
            $display("ie:%b oe:%b in:%b out1 act:%b exp:%b", ie[1], oe[1], in[1], out_1, bin_from_pad_out_1);
            $stop;
         end
         // Let's try all combination
         {ie, oe, in} <= {ie, oe, in} + 1;
       end
   end

endmodule

module pad(inout wire pad, input wire ie, input wire oe, input wire to_pad, output wire from_pad);

   assign pad = oe ? to_pad : 1'bz;
   assign from_pad = ie ? pad : 1'bz;
endmodule

module pad_binary(input wire pad_in,
                  output wire pad_out,
                  output wire pad_en,
                  input wire ie,
                  input wire oe,
                  input wire to_pad,
                  output from_pad_out,
                  output wire from_pad_en);

    assign pad_out = oe & to_pad;
    assign pad_en = oe;
    assign from_pad_out = ie & ((oe & to_pad) | pad_in);
    assign from_pad_en = ie;
endmodule
