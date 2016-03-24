// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Wilson Snyder

`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: Wrong parameter value", `__FILE__,`__LINE__); $stop; end while(0);

module t;
   parameter string1 = "Original String";
   parameter string2 = "Original String";

   parameter real11 = 0.1;
   parameter real12 = 0.1;
   parameter real21 = 0.1;
   parameter real22 = 0.1;
   parameter real31 = 0.1;
   parameter real32 = 0.1;

   parameter int11 = 1;
   parameter int12 = 1;
   parameter int21 = 1;
   parameter int22 = 1;
   parameter int31 = 1;
   parameter int32 = 1;
   parameter int41 = 1;
   parameter int42 = 1;

   initial begin
      `check(string1,"New String");
      `check(string2,"New String");
      `check(real11,0.2);
      `check(real12,0.2);
      `check(real21,400);
      `check(real22,400);
      `check(real31,20);
      `check(real32,20);
      `check(int11,16);
      `check(int12,16);
      `check(int21,16);
      `check(int22,16);
      `check(int31,123);
      `check(int32,123);
      `check(int41,32'hdeadbeef);
      `check(int42,32'hdeadbeef);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
