module counter(input clk, input rstn, output reg[3:0] out);
  always @(posedge clk) begin
    if (!rstn) out <= 0;
    else out <= out + 1;
  end
endmodule

module tb_counter;
  reg clk;
  reg rstn;
  wire [3:0] out;

  counter c(.clk (clk),
            .rstn (rstn),
            .out (out));

  always #5 begin
    if (clk) $write("[out] %d\n", out);
    clk = ~clk;
  end

  initial begin
    $dumpfile("file2.vcd");
    $dumpvars();
    #20 rstn <= 1;
    #20 clk <= 0;

    #25 rstn <= 1;
    #20 rstn <= 0;
    #10 rstn <= 1;

    #100 $finish;
  end
endmodule
