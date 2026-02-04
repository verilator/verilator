module test2 (
    input logic b
);
  logic do_something;
  assign do_something = b;
endmodule

module test (
    input logic a[2]  // unpacked array
);

  logic b[2];

  assign b = a;

  test2 i_test2 (.b);

endmodule
