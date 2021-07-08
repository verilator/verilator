// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Special cases of "string parameters" :
// This table compares obtain results from big-3 simulators to Verilator
// expected behavior. Base specified integer literals are also included as
// string detection may impact results for such cases.
//
// | Option/Param file   | simulator 1 | simulator 2 | simulator 3 | verilator   |
// |---------------------|-------------|-------------|-------------|-------------|
// | -gC0='"AB CD"'      | AB CD       | UNSUPPORTED | AB CD       | AB CD       |
// | -gC1=\"AB\ CD\"     | AB CD       | UNSUPPORTED | UNSUPPORTED | AB CD       |
// | -gC2="\"AB CD\""    | AB CD       | AB CD       | AB CD       | AB CD       |
// | -gC3="\"AB\ CD\""   | AB CD       | AB\\ CD     | AB CD       | AB CD       |
// | -gC4=32'h600D600D   | UNSUPPORTED | 32'h600D600D| 32'h600D600D| 32'h600D600D|
// | -gC5=32\'h600D600D  | 32'h600D600D| UNSUPPORTED | UNSUPPORTED | 32'h600D600D|
// | -gC6="32'h600D600D" | 32'h600D600D| 32'h600D600D| UNSUPPORTED | 32'h600D600D|
// | -gC7='AB CD'        | AB CD       | UNSUPPORTED | UNSUPPORTED | UNSUPPORTED |

`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: Wrong parameter value", `__FILE__,`__LINE__); $stop; end while(0);

module t;
   parameter string1 = "Original String";
   parameter string2 = "Original String";
   parameter string11 = "Original String";
   parameter string12 = "Original String";
   parameter string21 = "Original String";
   parameter string22 = "Original String";

   parameter real11 = 0.1;
   parameter real12 = 0.1;
   parameter real21 = 0.1;
   parameter real22 = 0.1;
   parameter real31 = 0.1;
   parameter real32 = 0.1;
   parameter real41 = 0.1;
   parameter real42 = 0.1;
   parameter real51 = 0.1;
   parameter real52 = 0.1;

   parameter int11 = 1;
   parameter int12 = 1;
   parameter int21 = 1;
   parameter int22 = 1;
   parameter int31 = 1;
   parameter int32 = 1;
   parameter int41 = 1;
   parameter int42 = 1;
   parameter int51 = 1;
   parameter int52 = 1;
   parameter int61 = 1;
   parameter int62 = 1;
   parameter int71 = 1;
   parameter int72 = 1;

   initial begin
      `check(string1,"New String");
      `check(string2,"New String");
      `check(string11,"New String");
      `check(string12,"New String");
      `check(string21,"New String");
      `check(string22,"New String");
      `check(real11,0.2);
      `check(real12,0.2);
      `check(real21,400);
      `check(real22,400);
      `check(real31,20);
      `check(real32,20);
      `check(real41,582.5);
      `check(real42,582.5);
      `check(real51,145.5);
      `check(real52,145.5);
      `check(int11,16);
      `check(int12,16);
      `check(int21,16);
      `check(int22,16);
      `check(int31,123);
      `check(int32,123);
      `check(int41,32'hdeadbeef);
      `check(int42,32'hdeadbeef);
      `check(int51,32'hdeadbeef);
      `check(int52,32'hdeadbeef);
      `check(int61,32'hdeadbeef);
      `check(int62,32'hdeadbeef);
      `check(int71,-1000);
      `check(int72,-1000);

      // Check parameter assigned simple integer literal is signed
      if ((int11 << 27) >>> 31 != -1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
