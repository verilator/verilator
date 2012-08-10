// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module init;
   
   task t1;
      reg 		 ba,bb,bc,bd,be,bf,bg,bh,bi,bj,bk,bl,bm,bn,bo,bp,bq,br,bs,bt,bu,bv,bw,bx,by,bz;
      reg 		 ca,cb,cc,cd,ce,cf,cg,ch,ci,cj,ck,cl,cm,cn,co,cp,cq,cr,cs,ct,cu,cv,cw,cx,cy,cz;
      reg 		 da,db,dc,dd,de,df,dg,dh,di,dj,dk,dl,dm,dn,   dp,dq,dr,ds,dt,du,dv,dw,dx,dy,dz;
      begin : READER
         $display ("Time: %0t  Instance: %m", $time);
      end
   endtask

   task t2;
      reg 		 ba,bb,bc,bd,be,bf,bg,bh,bi,bj,bk,bl,bm,bn,bo,bp,bq,br,bs,bt,bu,bv,bw,bx,by,bz;
      begin : READER
         $display ("Time: %0t  Instance: %m", $time);
      end
   endtask
endmodule

module test();
   init u_ram1();
   init u_ram2();
endmodule
