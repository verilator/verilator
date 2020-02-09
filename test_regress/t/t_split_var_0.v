// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA.

// If split_var pragma is removed, UNOPTFLAT appears.

module barshift_1d_unpacked #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = -3;
   logic [WIDTH-1:0] tmp[DEPTH+OFFSET:OFFSET]; /*verilator split_var*/
   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           if (shift[i]) begin
              tmp[i+1+OFFSET] = {tmp[i+OFFSET][(1 << i)-1:0], tmp[i+OFFSET][WIDTH-1:(2**i)]};
           end
           else begin
              tmp[i+1+OFFSET] = tmp[i+OFFSET];
           end
      end
   endgenerate
   assign tmp[0+OFFSET] = in;
   assign out = tmp[DEPTH+OFFSET];
endmodule


module barshift_1d_unpacked_le #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = -3;
   // almost same as above module, but tmp[smaller:bigger] here.
   logic [WIDTH-1:0] tmp[OFFSET:DEPTH+OFFSET]; /*verilator split_var*/
   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           if (shift[i]) begin
              tmp[i+1+OFFSET] = {tmp[i+OFFSET][(1 << i)-1:0], tmp[i+OFFSET][WIDTH-1:(2**i)]};
           end
           else begin
              tmp[i+1+OFFSET] = tmp[i+OFFSET];
           end
      end
   endgenerate
   assign tmp[0+OFFSET] = in;
   assign out = tmp[DEPTH+OFFSET];
endmodule


module barshift_1d_unpacked_struct0 #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = 1;
   typedef struct packed { logic [WIDTH-1:0] data; } data_type;
   data_type tmp[DEPTH+OFFSET:OFFSET]; /*verilator split_var*/
   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           if (shift[i]) begin
              tmp[i+1+OFFSET] = {tmp[i+OFFSET][(1 << i)-1:0], tmp[i+OFFSET][WIDTH-1:(2**i)]};
           end
           else begin
              tmp[i+1+OFFSET] = tmp[i+OFFSET];
           end
      end
   endgenerate
   assign tmp[0+OFFSET] = in;
   assign out = tmp[DEPTH+OFFSET];
endmodule


module barshift_2d_unpacked #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = 1;
   localparam N = 3;
   reg [WIDTH-1:0] tmp0[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp1[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp2[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1];
   reg [WIDTH-1:0] tmp3[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp4[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp5[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1];
   reg [WIDTH-1:0] tmp6[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/

   reg [WIDTH-1:0] tmp7[DEPTH+OFFSET+1:OFFSET+1][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp8[DEPTH+OFFSET+3:OFFSET-1][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp9[DEPTH+OFFSET+3:OFFSET+3][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp10[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   // because tmp11 is not split for testing mixture usage of split_var and no-spliv_ar,
   // UNOPTFLAT appears, but it's fine.
   /*verilator lint_off UNOPTFLAT*/
   reg [WIDTH-1:0] tmp11[-1:1][DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1];
   /*verilator lint_on UNOPTFLAT*/
   reg [WIDTH-1:0] tmp12[-1:0][DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/
   reg [WIDTH-1:0] tmp13[DEPTH+OFFSET:OFFSET][OFFSET:OFFSET+N-1]; /*verilator split_var*/

   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         for(genvar j = OFFSET; j < N + OFFSET; ++j) begin
            always_comb
              if (shift[i]) begin
                 tmp0[i+1+OFFSET][j] = {tmp0[i+OFFSET][j][(1 << i)-1:0], tmp0[i+OFFSET][j][WIDTH-1:(2**i)]};
              end
              else begin
                 tmp0[i+1+OFFSET][j] = tmp0[i+OFFSET][j];
              end
         end
      end
      for(genvar j = OFFSET; j < N + OFFSET; ++j) begin
         assign tmp0[0 + OFFSET][j] = in;
      end
   endgenerate
   assign tmp1 = tmp0;  // split both side
   assign tmp2 = tmp1;  // split only rhs
   assign tmp3 = tmp2;  // split only lhs
   always_comb tmp4 = tmp3; // split both side
   always_comb tmp5 = tmp4; // split only rhs
   always_comb tmp6 = tmp5; // split only lhs

   assign tmp7 = tmp6;
   assign tmp8[DEPTH+OFFSET+1:OFFSET+1] = tmp7;
   assign tmp9 = tmp8[DEPTH+OFFSET+1:OFFSET+1];
   assign tmp10[DEPTH+OFFSET:OFFSET] = tmp9[DEPTH+OFFSET+3:OFFSET+3];
   assign tmp11[1] = tmp10;
   assign tmp11[-1] = tmp11[1];
   assign tmp11[0] = tmp11[-1];
   assign tmp12 = tmp11[0:1];
   assign out = tmp12[1][DEPTH+OFFSET][OFFSET];
endmodule


module barshift_1d_unpacked_struct1 #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = 2;
   typedef struct packed { int data; } data_type;
   data_type tmp[DEPTH+OFFSET:OFFSET]; /*verilator split_var*/

   localparam [32-WIDTH-1:0] pad = 0;
   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           if (shift[i]) begin
              tmp[i+1+OFFSET] = {pad, tmp[i+OFFSET][(1 << i)-1:0], tmp[i+OFFSET][WIDTH-1:(2**i)]};
           end
           else begin
              tmp[i+1+OFFSET] = tmp[i+OFFSET];
           end
      end
   endgenerate
   assign tmp[0+OFFSET] = {pad, in};
   assign out = tmp[DEPTH+OFFSET][WIDTH-1:0];
endmodule


module barshift_2d_packed_array #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = -2;
   /*verilator lint_off LITENDIAN*/
   reg [OFFSET:DEPTH+OFFSET][WIDTH-1:0] tmp; /*verilator split_var*/
   /*verilator lint_on LITENDIAN*/

   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           /*verilator lint_off ALWCOMBORDER*/
           if (shift[i]) begin
              tmp[i+1+OFFSET] = {tmp[i+OFFSET][(1 << i)-1:0], tmp[i+OFFSET][WIDTH-1:(2**i)]};
           end
           else begin
              tmp[i+1+OFFSET][1:0]       = tmp[i+OFFSET][1:0];
              tmp[i+1+OFFSET][WIDTH-1:2] = tmp[i+OFFSET][WIDTH-1:2];
           end
         /*verilator lint_on ALWCOMBORDER*/
      end
   endgenerate
   assign tmp[0+OFFSET] = in;
   assign out = tmp[DEPTH+OFFSET];
endmodule


module barshift_2d_packed_array_le #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   localparam OFFSET = -2;
   /*verilator lint_off LITENDIAN*/
   reg [OFFSET:DEPTH+OFFSET][OFFSET:WIDTH-1+OFFSET] tmp; /*verilator split_var*/
   /*verilator lint_on LITENDIAN*/

   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           /*verilator lint_off ALWCOMBORDER*/
           if (shift[i]) begin
              tmp[i+1+OFFSET] = {tmp[i+OFFSET][WIDTH-(2**i)+OFFSET:WIDTH-1+OFFSET], tmp[i+OFFSET][OFFSET:WIDTH-(2**i)-1+OFFSET]};
           end
           else begin  // actulally just tmp[i+1+OFFSET] = tmp[i+OFFSET]
              tmp[i+1+OFFSET][0+OFFSET:2+OFFSET]  = tmp[i+OFFSET][0+OFFSET:2+OFFSET];
              tmp[i+1+OFFSET][3+OFFSET]           = tmp[i+OFFSET][3+OFFSET];
              {tmp[i+1+OFFSET][4+OFFSET],tmp[i+1+OFFSET][5+OFFSET]} = {tmp[i+OFFSET][4+OFFSET], tmp[i+OFFSET][5+OFFSET]};
              {tmp[i+1+OFFSET][7+OFFSET],tmp[i+1+OFFSET][6+OFFSET]} = {tmp[i+OFFSET][7+OFFSET], tmp[i+OFFSET][6+OFFSET]};
           end
         /*verilator lint_on ALWCOMBORDER*/
      end
   endgenerate
   assign tmp[0+OFFSET] = in;
   assign out = tmp[DEPTH+OFFSET];
endmodule


module barshift_1d_packed_struct #(localparam DEPTH = 3, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   typedef struct packed {
      logic [WIDTH-1:0] v0, v1, v2, v3;
   } data_type;
   wire data_type tmp; /*verilator split_var*/

   assign tmp.v0 = in;
   assign tmp.v1 = shift[0] == 1'b1 ? {tmp.v0[(1 << 0)-1:0], tmp.v0[WIDTH-1:2**0]} : tmp.v0;
   assign tmp.v2 = shift[1] == 1'b1 ? {tmp.v1[(1 << 1)-1:0], tmp.v1[WIDTH-1:2**1]} : tmp.v1;
   assign tmp.v3 = shift[2] == 1'b1 ? {tmp.v2[(1 << 2)-1:0], tmp.v2[WIDTH-1:2**2]} : tmp.v2;
   assign out = tmp.v3;
endmodule


module barshift_bitslice #(parameter DEPTH = 2, localparam WIDTH = 2**DEPTH)
   (input [WIDTH-1:0] in, input [DEPTH-1:0] shift, output [WIDTH-1:0] out);

   /*verilator lint_off LITENDIAN*/
   wire [0:WIDTH*(DEPTH+1) - 1] tmp; /*verilator split_var*/
   /*verilator lint_on LITENDIAN*/

   generate
      for(genvar i = 0; i < DEPTH; ++i) begin
         always_comb
           if (shift[i]) begin
              tmp[WIDTH*(i+1):WIDTH*(i+1+1)-1] = {tmp[WIDTH*(i+1)-(1<<i):WIDTH*(i+1)-1], tmp[WIDTH*i:WIDTH*i+((WIDTH-1) - (2**i))]};
           end
           else begin
              tmp[WIDTH*(i+1):WIDTH*(i+1+1)-1] = tmp[WIDTH*i:WIDTH*(i+1)-1];
           end
      end
   endgenerate
   assign tmp[WIDTH*0:WIDTH*(0+1)-1] = in;
   assign out = tmp[WIDTH*DEPTH:WIDTH*(DEPTH+1)-1];
endmodule


module var_decl_with_init();

   /*verilator lint_off LITENDIAN*/
   logic [-1:30] var0 = {4'd0, 4'd1, 4'd2, 4'd3, 4'd4, 4'd5, 4'd6, 4'd7}; /* verilator split_var */
   logic [-1:30] var2; /* verilator split_var */
   /*verilator lint_on LITENDIAN*/
   logic [30:-1] var1 = {4'd0, 4'd1, 4'd2, 4'd3, 4'd4, 4'd5, 4'd6, 4'd7}; /* verilator split_var */
   logic [30:-1] var3; /* verilator split_var */

   initial begin
      var2[-1:2] = 4'd2;
      var3[2:-1] = 4'd3;
      $display("%x %x", var0, var1);
      $display("%x %x", var2, var3);
      var0[-1:5] = 7'd0;
      var1[10:3] = 8'd2;
   end

endmodule


module t(/*AUTOARG*/ clk);
   input clk;
   localparam DEPTH = 3;
   localparam WIDTH = 2**DEPTH;
   localparam NUMSUB = 9;
   logic [WIDTH-1:0] in;
   logic [WIDTH-1:0] out[0:NUMSUB-1];
   logic [DEPTH-1:0] shift = 0;

   // barrel shifter
   barshift_1d_unpacked         #(.DEPTH(DEPTH)) shifter0(.in(in), .out(out[0]), .shift(shift));
   barshift_1d_unpacked_le      #(.DEPTH(DEPTH)) shifter1(.in(in), .out(out[1]), .shift(shift));
   barshift_1d_unpacked_struct0 #(.DEPTH(DEPTH)) shifter2(.in(in), .out(out[2]), .shift(shift));
   barshift_2d_unpacked         #(.DEPTH(DEPTH)) shifter3(.in(in), .out(out[3]), .shift(shift));
   barshift_1d_unpacked_struct1 #(.DEPTH(DEPTH)) shifter4(.in(in), .out(out[4]), .shift(shift));
   barshift_2d_packed_array     #(.DEPTH(DEPTH)) shifter5(.in(in), .out(out[5]), .shift(shift));
   barshift_2d_packed_array_le  #(.DEPTH(DEPTH)) shifter6(.in(in), .out(out[6]), .shift(shift));
   barshift_1d_packed_struct                     shifter7(.in(in), .out(out[7]), .shift(shift));
   barshift_bitslice            #(.DEPTH(DEPTH)) shifter8(.in(in), .out(out[8]), .shift(shift));
   var_decl_with_init i_var_decl_with_init();

   assign in = 8'b10001110;
   /*verilator lint_off LITENDIAN*/
   logic [7:0] [7:0] expc
               = {8'b10001110, 8'b01000111, 8'b10100011, 8'b11010001,
                  8'b11101000, 8'b01110100, 8'b00111010, 8'b00011101};
   /*verilator lint_on LITENDIAN*/
   always @(posedge clk) begin : always_block
      automatic bit failed = 0;
      $display("in:%b shift:%d expc:%b", in, shift, expc[7-shift]);
      for (int i = 0; i < NUMSUB; ++i) begin
         if (out[i] != expc[7-shift]) begin
            $display("Missmatch out[%d]:%b", i, out[i]);
            failed = 1;
         end
      end
      if (failed) $stop;
      if (shift == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      shift <= shift + 1;
   end

endmodule
