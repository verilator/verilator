// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Udi Finkelstein.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off MULTITOP */
// First, test we haven't broken normal ports
module t1();
endmodule

module t2;
endmodule

module t3(a);
input a;
endmodule

module t4(a, b);
input a, b;
endmodule

module t5(a,);
input a;
endmodule

module t6(a,,);
input a;
endmodule

module t7(a,b,);
input a, b;
endmodule

module t8(a,b,,);
input a, b;
endmodule

module t9(a,,b);
input a, b;
endmodule

module t10(a,,b,);
input a, b;
endmodule

module t11(a,,b,,);
input a, b;
endmodule

module t12(,a,,b);
input a, b;
endmodule

module t13(,a,,b,);
input a, b;
endmodule

module t14(,a,,b,,);
input a, b;
endmodule

module t15(,,a,,b);
input a, b;
endmodule

module t16(,,a,,b,);
input a, b;
endmodule

module t17(,,a,,b,,);
input a, b;
endmodule

module t18(,);
endmodule

/* verilator lint_off NULLPORT */
module t19(,,);
endmodule
