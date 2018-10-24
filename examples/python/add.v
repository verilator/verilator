//Adds a parameterised constant to an int

module add #(
    parameter integer N = 5
)(
    input reg rst,
    input reg clk,
    input integer value,
    output integer result
);

always @(posedge clk) begin
    if (rst) begin
        result <= 0;
    end else begin
        result <= value + N;
    end
end

endmodule
