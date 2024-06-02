// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off PINMISSING
// verilator lint_off WIDTHEXPAND

module t;
   // Original issue
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxxxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   // Change sizes
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/Xxxxxxxxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxxxxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxxxxxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );
   sub #(.PARAM("FALSE"))
     \$mul$/nxx_xxxxxxx/xxxxxxx/XxxxxxxxxxxXxxxxxxxxx/xxx/.././xxx/xxx_xxxxxxxxxx_xxxxx_xxxx_xxx_xxx.v:30$7  (
    );

endmodule

module sub #(parameter PARAM = "TRUE")
   (input [5:0]   ACC_FIR);
   always @(ACC_FIR) $display("WARNING: instance %m input is %d", PARAM);
endmodule
