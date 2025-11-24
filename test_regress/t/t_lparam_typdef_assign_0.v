
interface x_if #(
   parameter int p_awidth = 4
   ,parameter int p_dwidth = 7
)();
   typedef struct packed {
      logic [p_awidth-1:0] addr;
      logic [p_dwidth-1:0] data;
   } rq_t;

   typedef struct packed {
      logic [p_dwidth-1:0] data;
   } rs_t;
endinterface

module top();
   x_if #(
      .p_awidth(16)
      ,.p_dwidth(8)
   ) if0();

   localparam p0_rq_t = if0.rq_t;
   localparam p0_rs_t = if0.rs_t;

   p0_rq_t rq;
   p0_rs_t rs;

   always_comb begin
      rq.addr = 'h1234;
      rq.data = 'h37;
      rs.data = 'h5a;
   end

   initial begin
      #1;
      if(rq.addr != 16'h1234) $stop;
      if(rq.data != 8'h37) $stop;
      if(rs.data != 8'h5a) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
