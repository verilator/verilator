module tb_counter;
  reg clk;
  reg rstn;
  reg [3:0] out;

  always @(posedge clk) begin
    if (!rstn) out <= 0;
    else out <= out + 1;
  end

  always #5 begin
    if (clk) $write("[out] %d\n", out);
    clk = ~clk;
  end

  initial begin
    $dumpfile("file2.vcd");
    $dumpvars();
    clk <= 0;

    #20 rstn <= 0;
    #10 rstn <= 1;
    #80 out <= 'x;

    #20 $finish;
  end
endmodule
