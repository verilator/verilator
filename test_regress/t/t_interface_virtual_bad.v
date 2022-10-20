// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Arkadiusz Kozdra.
// SPDX-License-Identifier: CC0-1.0

// See also t_interface_virtual.v

interface PBus;
   logic req, grant;
   logic [7:0] addr, data;
   modport phy(input addr, ref data);
endinterface

interface QBus;
endinterface

typedef virtual PBus vpbus_t;

module t (/*AUTOARG*/);

   PBus p8;
   QBus q8;
   vpbus_t v8;
   virtual PBus.phy v8_phy;
   logic data;

   initial begin
      v8 = p8;
      p8 = v8;  // error
      v8 = q8;  // error
      v8_phy = p8;
      v8_phy = v8;
      v8_phy = p8.phy;
      v8 = v8_phy;  // error
      v8 = p8.phy;  // error
      data = p8.phy;  // error
      data = v8_phy;  // error
      data = v8;  // error
      data = p8;  // error
      v8 = data;  // error
      v8.grant = 1'b1;

      $display("q8.grant=", p8.grant, " v8.grant=", v8.grant, v8_phy.addr, v8.gran);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
