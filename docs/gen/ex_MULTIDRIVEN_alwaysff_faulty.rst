.. code-block:: sv
    :linenos:
    :emphasize-lines: 3,6

    module t(input logic clk, input logic d, output logic q);

        initial q = 1'b0;  // <--- Warning

        always_ff @(posedge clk) begin
        q <= d;  // <--- Warning
        end
    endmodule
