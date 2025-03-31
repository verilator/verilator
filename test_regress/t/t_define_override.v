`define TEST_MACRO 10
`define TEST_MACRO 100
module test (
);
    initial begin
        $display("TEST_MACRO %d", `TEST_MACRO);
        $finish;
    end

endmodule
