module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int pos;
   int a;
   int b;
   int array[2][2] = '{ '{0, 1}, '{2, 3}};

   string test_string = "abcd";

   initial begin
      if (0 && test_string[pos++] != "e");
      if (1 || pos-- != 1);

      if (a <-> --b);
      if (0 -> ++b);

      pos = (a > 0) ? a++ : --b;

      pos = array[0][0]++;
   end
endmodule
