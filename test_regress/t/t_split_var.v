module barshift #(parameter depth = 2, localparam width = 2**depth) (
    input [width-1:0] in, input [depth-1:0] shift, output [width-1:0]out);

// If the following split_array var is removed, ALWCOMBORDER and UNOPTFLAT appear.
logic [width-1:0] tmp[0:depth]; /*verilator split_var*/
generate
    for(genvar i = 0; i < depth; ++i) begin
        always_comb
        if (shift[i]) begin
            tmp[i+1] = {tmp[i][(1 << i)-1:0], tmp[i][width-1:(2**i)]};
        end else begin
            tmp[i + 1] = tmp[i];
        end
    end
endgenerate
assign tmp[0] = in;
assign out = tmp[depth];
endmodule


module t(/*AUTOARG*/ clk);
input clk;
localparam depth = 3;
localparam width = 2**depth;
logic [width-1:0] in, out0;
logic [depth-1:0] shift = 0;

`ifndef VERILATOR
// The following variables can not be splitted. will see warnings.
logic should_show_warning0; /*verilator split_var*/
logic [1:0][7:0]should_show_warning1; /*verilator split_var*/
logic [7:0]should_show_warning2[0:1][0:3]; /*verilator split_var*/
`endif

// barrel shifter
barshift #(.depth(depth)) shifter0(.in(in), .out(out0), .shift(shift));

assign in = 8'b10001110;
always @(posedge clk) begin
    $display("in:%b shift:%d out:%b", in, shift, out0);
    if (&shift) begin
        $write("*-* All Finished *-*\n");
        $finish;
    end
    shift <= shift + 1;
end

endmodule
