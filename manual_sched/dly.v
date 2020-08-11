module top(output reg a, input wire b, output reg c, input wire clk1, output reg d, output wire e, input wire f);
    reg clk;

    assign e = f;

    always begin
        #20
        clk = 0;
        #20
        clk = 1;
    end

    initial begin
        $display("TOP");
    end

    always @(posedge clk)
        if (b) $finish;

    always @(posedge clk)
        $display("other block0 %d %d", a, c);

    always @(posedge clk) begin
        a <= ~a;
        $display("same block0 %d %d", a, c);
    end

    always @(posedge clk1) begin
        $display("clk1 %d", d);
        d <= ~d;
    end

    always @(posedge clk) begin
        c <= a;
        $display("same block1 %d %d", a, c);
    end

    always @(posedge clk)
        $display("other block2 %d %d\n", a, c);


    assert property (@(posedge clk) a == b);

    prog pr_1 (clk, a, b);

endmodule

program prog(input wire clk, input wire a, input wire b, input wire [7:0] c);

    assert property (@(posedge clk) c == b + 2);

    initial
        $display("PRG");

endprogram
