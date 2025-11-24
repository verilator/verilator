
interface bus_if #(
   parameter int p_awidth = 4
   ,parameter int p_dwidth = 7
);
   typedef struct packed {
      logic [p_awidth-1:0] addr;
   } rq_t;
endinterface

module a_mod(
   bus_if bus_io
);
   localparam bus_rq_t = bus_io.rq_t;
endmodule

module top();
   bus_if #(.p_awidth(16), .p_dwidth(8)) bus_io();

   a_mod a_mod_inst(
      .bus_io(bus_io)
   );

   initial begin
      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
