module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   string test_string = "abcd";

   int array3d[2][3][4] = '{
                             '{
                                '{  0,  1,  2,  3},
                                '{  4,  5,  6,  7},
                                '{  8,  9, 10, 11}
                              },
                             '{
                                '{ 12, 13, 14, 15},
                                '{ 16, 17, 18, 19},
                                '{ 20, 21, 22, 23}
                              }
                           };
   int pos;
   int val;
   int i;
   byte b;

   int data[4] = '{1, 2, 3, 4};

   generate
      genvar j;
      int gdata[4];
      for (j=0; j < 5; j++) begin
         initial if (j >= 5) $stop;
      end

      for (j=0; j < 5; ++j) begin
         initial if (j >= 5) $stop;
      end

      for (j=10; j >= 5; j--) begin
         initial if (j < 5) $stop;
      end

      for (j=10; j >= 5; --j) begin
         initial if (j < 5) $stop;
      end
   endgenerate

   initial begin
      pos = 0;
      pos++;
      if (pos != 1) $stop;

      array3d[0][0][0]++;
      if (array3d[0][0][0] != 1) $stop;

      --array3d[0][0][0];
      if (array3d[0][0][0] != 0) $stop;

      pos = 2;
      b = test_string[--pos];
      if (b !== "b") $stop;
      if (pos !== 1) $stop;

      pos = 1;
      b = test_string[++pos];
      if (b !== "c") $stop;
      if (pos !== 2) $stop;

      pos = 3;
      b = test_string[pos--];
      if (b !== "d") $stop;
      if (pos !== 2) $stop;

      pos = 0;
      b = test_string[pos++];
      if (b !== "a") $stop;
      if (pos !== 1) $stop;

      pos = 0;
      val = array3d[++pos][--pos][++pos];
      if (pos !== 1) $stop;
      if (val !== 13) $stop;

      pos = 0;
      val = array3d[++pos][pos--][++pos];
      if (pos !== 1) $stop;
      if (val !== 17) $stop;

      for (i=0; data[++i]<4;) begin
         // loop with multiple statements
         pos = i;
         val = data[i];
      end

      if (pos !== 2) $stop;
      if (i !== 3) $stop;
      if (val !== 3) $stop;

      i = 0;
      while (data[i++]<4) begin
         // loop with multiple statements
         pos = i;
         val = data[i];
      end

      if (pos !== 3) $stop;
      if (i !== 4) $stop;
      if (val !== 4) $stop;


      pos = 0;
      if (1 == 1) begin
         pos++;
      end
      if (pos != 1) $stop;

      pos = 0;
      if (1 == 1) pos++;
      if (pos != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;

   end
endmodule
