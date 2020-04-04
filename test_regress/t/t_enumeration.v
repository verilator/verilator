// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cnt = 0;
   integer mod = 0;

   // event counter
   always @ (posedge clk)
   if (cnt==20) begin
      cnt <= 0;
      mod <= mod + 1;
   end else begin
      cnt <= cnt + 1;
   end

   // finish report
   always @ (posedge clk)
   if (mod==3) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   // anonymous type variable declaration
   enum logic [2:0] {red=1, orange, yellow, green, blue, indigo, violet} rainbow7;

   // named type
   typedef enum logic {OFF, ON} t_switch;
   t_switch switch;

   // numbering examples
   enum integer {father, mother, son[2], daughter, gerbil, dog[3]=10, cat[3:5]=20, car[3:1]=30} family;

   // test of raibow7 type
   always @ (posedge clk)
   if (mod==0) begin
      // write value to array
      if      (cnt== 0)  begin
         rainbow7 <= rainbow7.first();
         // check number
         if (rainbow7.num()  !== 7      ) begin $display("%d", rainbow7.num() ); $stop(); end
         if (rainbow7        !== 3'bxxx ) begin $display("%b", rainbow7       ); $stop(); end
      end
      else if (cnt== 1)  begin
         if (rainbow7        !== 3'd1   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== red    ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 2)  begin
         if (rainbow7        !== 3'd2   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== orange ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 3)  begin
         if (rainbow7        !== 3'd3   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== yellow ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 4)  begin
         if (rainbow7        !== 3'd4   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== green  ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 5)  begin
         if (rainbow7        !== 3'd5   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== blue   ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 6)  begin
         if (rainbow7        !== 3'd6   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== indigo ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 7)  begin
         if (rainbow7        !== 3'd7   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== violet ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
      else if (cnt== 8)  begin
         if (rainbow7        !== 3'd1   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== red    ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.next();
      end
   end else if (mod==1) begin
      // write value to array
      if      (cnt== 0)  begin
         rainbow7 <= rainbow7.last();
         // check number
         if (rainbow7.num()  !== 7      ) begin $display("%d", rainbow7.num() ); $stop(); end
      end
      else if (cnt== 1)  begin
         if (rainbow7        !== 3'd7   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== violet ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 2)  begin
         if (rainbow7        !== 3'd6   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== indigo ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 3)  begin
         if (rainbow7        !== 3'd5   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== blue   ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 4)  begin
         if (rainbow7        !== 3'd4   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== green  ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 5)  begin
         if (rainbow7        !== 3'd3   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== yellow ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 6)  begin
         if (rainbow7        !== 3'd2   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== orange ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 7)  begin
         if (rainbow7        !== 3'd1   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== red    ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
      else if (cnt== 8)  begin
         if (rainbow7        !== 3'd7   ) begin $display("%b", rainbow7       ); $stop(); end
         if (rainbow7        !== violet ) begin $display("%b", rainbow7       ); $stop(); end
         rainbow7 <= rainbow7.prev();
      end
   end

   // test of t_switch type
   always @ (posedge clk)
   if (mod==0) begin
      // write value to array
      if      (cnt== 0)  begin
         switch <= switch.first();
         // check number
         if (switch.num()  !== 2   ) begin $display("%d", switch.num() ); $stop(); end
         if (switch        !== 1'bx) begin $display("%b", switch       ); $stop(); end
      end
      else if (cnt== 1)  begin
         if (switch        !== 1'b0) begin $display("%b", switch       ); $stop(); end
         if (switch        !== OFF ) begin $display("%b", switch       ); $stop(); end
         switch <= switch.next();
      end
      else if (cnt== 2)  begin
         if (switch        !== 1'b1) begin $display("%b", switch       ); $stop(); end
         if (switch        !== ON  ) begin $display("%b", switch       ); $stop(); end
         switch <= switch.next();
      end
      else if (cnt== 3)  begin
         if (switch        !== 1'b0) begin $display("%b", switch       ); $stop(); end
         if (switch        !== OFF ) begin $display("%b", switch       ); $stop(); end
         switch <= switch.next();
      end
   end else if (mod==1) begin
      // write value to array
      if      (cnt== 0)  begin
         rainbow7 <= rainbow7.last();
         // check number
         if (switch.num()  !== 2   ) begin $display("%d", switch.num() ); $stop(); end
      end
      else if (cnt== 1)  begin
         if (switch        !== 1'b1) begin $display("%b", switch       ); $stop(); end
         if (switch        !== ON  ) begin $display("%b", switch       ); $stop(); end
         switch <= switch.prev();
      end
      else if (cnt== 2)  begin
         if (switch        !== 1'b0) begin $display("%b", switch       ); $stop(); end
         if (switch        !== OFF ) begin $display("%b", switch       ); $stop(); end
         switch <= switch.prev();
      end
      else if (cnt== 3)  begin
         if (switch        !== 1'b1) begin $display("%b", switch       ); $stop(); end
         if (switch        !== ON  ) begin $display("%b", switch       ); $stop(); end
         switch <= switch.prev();
      end
   end

   // test of raibow7 type
   always @ (posedge clk)
   if (mod==0) begin
      // write value to array
      if      (cnt== 0)  begin
         family <= family.first();
         // check number
         if (family.num()  !== 15       ) begin $display("%d", family.num() ); $stop(); end
         if (family        !== 32'dx    ) begin $display("%b", family       ); $stop(); end
      end
      else if (cnt== 1)  begin
         if (family        !== 0        ) begin $display("%b", family       ); $stop(); end
         if (family        !== father   ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 2)  begin
         if (family        !== 1        ) begin $display("%b", family       ); $stop(); end
         if (family        !== mother   ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 3)  begin
         if (family        !== 2        ) begin $display("%b", family       ); $stop(); end
         if (family        !== son0     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 4)  begin
         if (family        !== 3        ) begin $display("%b", family       ); $stop(); end
         if (family        !== son1     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 5)  begin
         if (family        !== 4        ) begin $display("%b", family       ); $stop(); end
         if (family        !== daughter ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 6)  begin
         if (family        !== 5        ) begin $display("%b", family       ); $stop(); end
         if (family        !== gerbil   ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 7)  begin
         if (family        !== 10       ) begin $display("%b", family       ); $stop(); end
         if (family        !== dog0     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 8)  begin
         if (family        !== 11       ) begin $display("%b", family       ); $stop(); end
         if (family        !== dog1     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 9)  begin
         if (family        !== 12       ) begin $display("%b", family       ); $stop(); end
         if (family        !== dog2     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 10)  begin
         if (family        !== 20       ) begin $display("%b", family       ); $stop(); end
         if (family        !== cat3     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 11)  begin
         if (family        !== 21       ) begin $display("%b", family       ); $stop(); end
         if (family        !== cat4     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 12)  begin
         if (family        !== 22       ) begin $display("%b", family       ); $stop(); end
         if (family        !== cat5     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 13)  begin
         if (family        !== 30       ) begin $display("%b", family       ); $stop(); end
         if (family        !== car3     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 14)  begin
         if (family        !== 31       ) begin $display("%b", family       ); $stop(); end
         if (family        !== car2     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
      else if (cnt== 15)  begin
         if (family        !== 32       ) begin $display("%b", family       ); $stop(); end
         if (family        !== car1     ) begin $display("%b", family       ); $stop(); end
         family <= family.next();
      end
   end
endmodule
