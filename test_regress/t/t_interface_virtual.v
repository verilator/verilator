// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Arkadiusz Kozdra.
// SPDX-License-Identifier: CC0-1.0

// See also t_interface_virtual_bad.v

interface PBus;
   logic req, grant;
   logic [7:0] addr, data;
   modport phy(input addr, ref data);
endinterface

class Cls;
   virtual PBus fa, fb;
endclass

module t (/*AUTOARG*/);

   PBus ia, ib;
   virtual PBus va, vb;
   virtual PBus.phy pa, pb;
   Cls ca, cb;

   initial begin
      va = ia;
      vb = ib;

      ca = new;
      cb = new;

      va.addr = 8'haa;
      ia.data = 8'h11;

      vb.addr = 8'hbb;
      ib.data = 8'h22;

      $display("va.addr=%x", va.addr, " va.data=%x", va.data, " ia.addr=%x", ia.addr, " ia.data=%x", ia.data);
      $display("vb.addr=%x", vb.addr, " vb.data=%x", vb.data, " ib.addr=%x", ib.addr, " ib.data=%x", ib.data);

      ca.fa = ia;
      ca.fb = ib;
      cb.fa = ib;
      cb.fb = ia;
//      pa = va;
//      pb = vb;

//      pb.addr = 8'hb0;
//      pa.addr = 8'ha0;

      $display("ca.fa.addr=%x", ca.fa.addr, " ca.fa.data=%x", ca.fa.data, " ca.fa.addr=%x", ca.fb.addr, " ca.fb.data=%x", ca.fb.data);
      $display("cb.fa.addr=%x", cb.fa.addr, " cb.fa.data=%x", cb.fa.data, " cb.fa.addr=%x", cb.fb.addr, " cb.fb.data=%x", cb.fb.data);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
