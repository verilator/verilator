// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

program t;
   parameter SIZE = 5;

   typedef reg [SIZE-1:0] vec_t ;
   vec_t a; initial a =0;

   typedef bit [SIZE-1:0] vec_bit_t ;
   vec_bit_t b; initial b =0;

   typedef int array [3];
   typedef array array2 [2];
   array2 ar [1];

   // Define before use
   // Not sure how well supported this is elsewhere
   //UNSUP typedef preuse;
   //UNSUP preuse p;
   //UNSUP typedef int preuse;

//reg [SIZE-1:0] a; initial a =0;
//reg [SIZE-1:0] b; initial b =0;

   initial begin
      typedef logic [3:0][7:0] instr_mem_t;
      instr_mem_t a;
      a[0] = 8'h12;
      if (a[0] != 8'h12) $stop;
   end

   integer j;
   initial begin
      for (j=0;j<=(1<<SIZE);j=j+1) begin
         a = a + 1;
         b = b + 1;
         //$write("a=%d \t b=%d \n", a,b);
      end

      if (a != 1 ) begin
         $write("a=%d \n", a);
         $stop;
      end
      if (b != 1 ) begin
         $write("b=%d \n", b);
         $stop;
      end

      ar[0][0][0] = 0;
      ar[0][0][2] = 2;
      ar[0][1][0] = 3;
      ar[0][1][2] = 5;
      if (ar[0][0][0] !== 0) $stop;
      if (ar[0][0][2] !== 2) $stop;
      if (ar[0][1][0] !== 3) $stop;
      if (ar[0][1][2] !== 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endprogram
