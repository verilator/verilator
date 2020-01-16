// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA.

// If split_var pragma is removed, UNOPTFLAT appears.

module barshift_1d_unpacked #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    localparam offset = -3;
    logic [width-1:0] tmp[depth+offset:offset]; /*verilator split_var*/
    generate
        for(genvar i = 0; i < depth; ++i) begin
            always_comb
            if (shift[i]) begin
                tmp[i+1+offset] = {tmp[i+offset][(1 << i)-1:0], tmp[i+offset][width-1:(2**i)]};
            end else begin
                tmp[i+1+offset] = tmp[i+offset];
            end
        end
    endgenerate
    assign tmp[0+offset] = in;
    assign out = tmp[depth+offset];
endmodule


module barshift_1d_unpacked_struct0 #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    localparam offset = 1;
    typedef struct packed { logic [width-1:0] data; } data_type;
    data_type tmp[depth+offset:offset]; /*verilator split_var*/
    generate
        for(genvar i = 0; i < depth; ++i) begin
            always_comb
            if (shift[i]) begin
                tmp[i+1+offset] = {tmp[i+offset][(1 << i)-1:0], tmp[i+offset][width-1:(2**i)]};
            end else begin
                tmp[i+1+offset] = tmp[i+offset];
            end
        end
    endgenerate
    assign tmp[0+offset] = in;
    assign out = tmp[depth+offset];
endmodule


module barshift_2d_unpacked #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    localparam offset = 1;
    localparam n = 3;
    reg [width-1:0]tmp0[depth+offset:offset][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp1[depth+offset:offset][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp2[depth+offset:offset][offset:offset+n-1];
    reg [width-1:0]tmp3[depth+offset:offset][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp4[depth+offset:offset][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp5[depth+offset:offset][offset:offset+n-1];
    reg [width-1:0]tmp6[depth+offset:offset][offset:offset+n-1]; /*verilator split_var*/

    reg [width-1:0]tmp7[depth+offset+1:offset+1][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp8[depth+offset+3:offset-1][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp9[depth+offset+3:offset+3][offset:offset+n-1]; /*verilator split_var*/
    reg [width-1:0]tmp10[depth+offset:offset][offset:offset+n-1]; /*verilator split_var*/

    generate
        for(genvar i = 0; i < depth; ++i) begin
            for(genvar j = offset; j < n + offset; ++j) begin
                always_comb
                    if (shift[i]) begin
                        tmp0[i+1+offset][j] = {tmp0[i+offset][j][(1 << i)-1:0], tmp0[i+offset][j][width-1:(2**i)]};
                    end else begin
                        tmp0[i+1+offset][j] = tmp0[i+offset][j];
                    end
            end
        end
        for(genvar j = offset; j < n + offset; ++j) begin
            assign tmp0[0 + offset][j] = in;
        end
    endgenerate
    assign tmp1 = tmp0;  // split both side
    assign tmp2 = tmp1;  // split only rhs
    assign tmp3 = tmp2;  // split only lhs
    always_comb tmp4 = tmp3; // split both side
    always_comb tmp5 = tmp4; // split only rhs
    always_comb tmp6 = tmp5; // split only lhs

    assign tmp7 = tmp6;
    assign tmp8[depth+offset+1:offset+1] = tmp7;
    assign tmp9 = tmp8[depth+offset+1:offset+1];
    assign tmp10[depth+offset:offset] = tmp9[depth+offset+3:offset+3];
    assign out = tmp10[depth+offset][offset];
endmodule


module barshift_1d_unpacked_struct1 #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    localparam offset = 2;
    typedef struct packed { int data; } data_type;
    data_type tmp[depth+offset:offset]; /*verilator split_var*/

    localparam [32-width-1:0] pad = 0;
    generate
        for(genvar i = 0; i < depth; ++i) begin
            always_comb
            if (shift[i]) begin
                tmp[i+1+offset] = {pad, tmp[i+offset][(1 << i)-1:0], tmp[i+offset][width-1:(2**i)]};
            end else begin
                tmp[i+1+offset] = tmp[i+offset];
            end
        end
    endgenerate
    assign tmp[0+offset] = {pad, in};
    assign out = tmp[depth+offset][width-1:0];
endmodule


module barshift_2d_packed_array #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    localparam offset = -2;
    /*verilator lint_off LITENDIAN*/
    reg [offset:depth+offset][width-1:0] tmp; /*verilator split_var*/
    /*verilator lint_on LITENDIAN*/

    generate
        for(genvar i = 0; i < depth; ++i) begin
            always_comb
            /*verilator lint_off ALWCOMBORDER*/
            if (shift[i]) begin
                tmp[i+1+offset] = {tmp[i+offset][(1 << i)-1:0], tmp[i+offset][width-1:(2**i)]};
            end else begin
                tmp[i+1+offset][1:0]       = tmp[i+offset][1:0];
                tmp[i+1+offset][width-1:2] = tmp[i+offset][width-1:2];
            end
            /*verilator lint_on ALWCOMBORDER*/
        end
    endgenerate
    assign tmp[0+offset] = in;
    assign out = tmp[depth+offset];
endmodule


module barshift_2d_packed_array_le #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    localparam offset = -2;
    /*verilator lint_off LITENDIAN*/
    reg [offset:depth+offset][offset:width-1+offset] tmp; /*verilator split_var*/
    /*verilator lint_on LITENDIAN*/

    generate
        for(genvar i = 0; i < depth; ++i) begin
            always_comb
            /*verilator lint_off ALWCOMBORDER*/
            if (shift[i]) begin
                tmp[i+1+offset] = {tmp[i+offset][width-(2**i)+offset:width-1+offset], tmp[i+offset][offset:width-(2**i)-1+offset]};
            end else begin  // actulally just tmp[i+1+offset] = tmp[i+offset]
                tmp[i+1+offset][0+offset:2+offset]  = tmp[i+offset][0+offset:2+offset];
                tmp[i+1+offset][3+offset]           = tmp[i+offset][3+offset];
                {tmp[i+1+offset][4+offset],tmp[i+1+offset][5+offset]} = {tmp[i+offset][4+offset], tmp[i+offset][5+offset]};
                {tmp[i+1+offset][7+offset],tmp[i+1+offset][6+offset]} = {tmp[i+offset][7+offset], tmp[i+offset][6+offset]};
            end
            /*verilator lint_on ALWCOMBORDER*/
        end
    endgenerate
    assign tmp[0+offset] = in;
    assign out = tmp[depth+offset];
endmodule


module barshift_1d_packed_struct #(localparam depth = 3, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    typedef struct packed {
        logic [width-1:0] v0, v1, v2, v3;
    } data_type;
    wire data_type tmp; /*verilator split_var*/

    assign tmp.v0 = in;
    assign tmp.v1 = shift[0] == 1'b1 ? {tmp.v0[(1 << 0)-1:0], tmp.v0[width-1:2**0]} : tmp.v0;
    assign tmp.v2 = shift[1] == 1'b1 ? {tmp.v1[(1 << 1)-1:0], tmp.v1[width-1:2**1]} : tmp.v1;
    assign tmp.v3 = shift[2] == 1'b1 ? {tmp.v2[(1 << 2)-1:0], tmp.v2[width-1:2**2]} : tmp.v2;
    assign out = tmp.v3;
endmodule


module barshift_bitslice #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

    /*verilator lint_off LITENDIAN*/
    wire [0:width*(depth+1) - 1] tmp; /*verilator split_var*/
    /*verilator lint_on LITENDIAN*/

    generate
        for(genvar i = 0; i < depth; ++i) begin
            always_comb
            if (shift[i]) begin
                tmp[width*(i+1):width*(i+1+1)-1] = {tmp[width*(i+1)-(1<<i):width*(i+1)-1], tmp[width*i:width*i+((width-1) - (2**i))]};
            end else begin
                tmp[width*(i+1):width*(i+1+1)-1] = tmp[width*i:width*(i+1)-1];
            end
        end
    endgenerate
    assign tmp[width*0:width*(0+1)-1] = in;
    assign out = tmp[width*depth:width*(depth+1)-1];
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
    localparam depth = 3;
    localparam width = 2**depth;
    localparam numsub = 8;
    logic [width-1:0] in;
    logic [width-1:0] out[0:numsub-1];
    logic [depth-1:0] shift = 0;

    // barrel shifter
    barshift_1d_unpacked         #(.depth(depth)) shifter0(.in(in), .out(out[0]), .shift(shift));
    barshift_1d_unpacked_struct0 #(.depth(depth)) shifter1(.in(in), .out(out[1]), .shift(shift));
    barshift_2d_unpacked         #(.depth(depth)) shifter2(.in(in), .out(out[2]), .shift(shift));
    barshift_1d_unpacked_struct1 #(.depth(depth)) shifter3(.in(in), .out(out[3]), .shift(shift));
    barshift_2d_packed_array     #(.depth(depth)) shifter4(.in(in), .out(out[4]), .shift(shift));
    barshift_2d_packed_array_le  #(.depth(depth)) shifter5(.in(in), .out(out[5]), .shift(shift));
    barshift_1d_packed_struct                     shifter6(.in(in), .out(out[6]), .shift(shift));
    barshift_bitslice            #(.depth(depth)) shifter7(.in(in), .out(out[7]), .shift(shift));
    var_decl_with_init i_var_decl_with_init();

    assign in = 8'b10001110;
    /*verilator lint_off LITENDIAN*/
    logic [7:0] [7:0] exp = {
        8'b10001110, 8'b01000111, 8'b10100011, 8'b11010001,
        8'b11101000, 8'b01110100, 8'b00111010, 8'b00011101};
    /*verilator lint_on LITENDIAN*/
    always @(posedge clk) begin : always_block
        automatic bit failed = 0;
        $display("in:%b shift:%d exp:%b", in, shift, exp[7-shift]);
        for (int i = 0; i < numsub; ++i) begin
            if (out[i] != exp[7-shift]) begin
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
