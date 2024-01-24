// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   interface class Courier;
      pure virtual function void deliver();
   endclass
   class Person implements Courier;
      virtual function void deliver();
         $display("slow delivery");
      endfunction
   endclass

   interface class Seats;
      pure virtual function int seats();
   endclass

   class Vehicle;
   endclass

   class Car extends Vehicle implements Courier, Seats;
      virtual function void deliver();
         $display("fast delivery");
      endfunction
      virtual function int seats(); return 4; endfunction
   endclass

   class MetaCar extends Car;
   endclass

   function void do_delivery(Courier courier);
      courier.deliver();
   endfunction

   initial begin
      MetaCar car;
      car = new();
      do_delivery(car);
      if (car.seats() != 4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
