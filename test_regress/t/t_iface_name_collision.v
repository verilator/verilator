/* verilator lint_off DECLFILENAME */
/* verilator lint_off UNUSEDSIGNAL */
interface avst_interface;
  logic ready;
  logic valid;

  modport sink_mp (output ready, input  valid);
endinterface

module child (
  output logic ready_out
);
  avst_interface my_avst_if();

  assign ready_out = my_avst_if.ready;
  assign my_avst_if.ready = 1'b1; // drives child.my_avst_if.ready only
endmodule

module wrapper (
  avst_interface.sink_mp my_avst_if
);
  child child_inst (
    .ready_out (my_avst_if.ready) // sole driver of outer my_avst_if.ready
  );
endmodule

module top (
  input  logic in_valid,
  output logic out_ready
);
  avst_interface my_avst_if();

  assign my_avst_if.valid = in_valid;
  assign out_ready = my_avst_if.ready;

  wrapper wrapper_inst (.my_avst_if (my_avst_if));
endmodule
