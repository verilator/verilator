// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// This checks IEEE ports work correctly, we use XML output to make it easy to
// see all attributes are propagated

// verilator lint_off MULTITOP

`ifndef VERILATOR
module mh0 (wire x_inout_wire_logic);
endmodule
module mh1 (integer x_inout_wire_integer);
endmodule
`endif
module mh2 (inout integer x_inout_wire_integer);
endmodule
`ifndef VERILATOR
module mh3 ([5:0] x_inout_wire_logic_p6);
endmodule
`endif
module mh5 (input x_input_wire_logic);
endmodule
module mh6 (input var x_input_var_logic);
endmodule
module mh7 (input var integer x_input_var_integer);
endmodule
module mh8 (output x_output_wire_logic);
endmodule
module mh9 (output var x_output_var_logic);
endmodule
module mh10(output signed [5:0] x_output_wire_logic_signed_p6);
endmodule
module mh11(output integer x_output_var_integer);
endmodule
module mh12(ref [5:0] x_ref_logic_p6);
endmodule
module mh13(ref x_ref_var_logic_u6 [5:0]);
endmodule
`ifndef VERILATOR
module mh14(wire x_inout_wire_logic, y_inout_wire_logic_p8 [7:0]);
endmodule
module mh15(integer x_inout_wire_integer, signed [5:0] y_inout_wire_logic_signed6);
endmodule
module mh16([5:0] x_inout_wire_logic_p6, wire y_inout_wire_logic);
endmodule
`endif
module mh17(input var integer x_input_var_integer, wire y_input_wire_logic);
endmodule
module mh18(output var x_output_var_logic, input y_input_wire_logic);
endmodule
module mh19(output signed [5:0] x_output_wire_logic_signed_p6, integer y_output_var_integer);
endmodule
module mh20(ref [5:0] x_ref_var_logic_p6, y_ref_var_logic_p6);
endmodule
module mh21(ref ref_var_logic_u6 [5:0], y_ref_var_logic);
endmodule
