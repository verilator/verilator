
interface y_if #(
   parameter int p_awidth = 3
)();
   typedef struct packed {
      logic [p_awidth-1:0] addr;
   } rq2_t;
endinterface

interface x_if #(
   parameter int p_awidth = 4
   ,parameter int p_dwidth = 7
)();
   typedef struct packed {
      logic [p_awidth-1:0] addr;
   } rq_t;

   typedef struct packed {
      logic [p_dwidth-1:0] data;
   } rs_t;

   y_if#(.p_awidth(p_awidth)) y_if0();

endinterface

module top();
   x_if #(
      .p_awidth(16)
      ,.p_dwidth(8)
   ) if0();

   localparam p0_rq2_t = if0.y_if0.rq2_t;
   localparam p0_rq_t = if0.rq_t;
   localparam p0_rs_t = if0.rs_t;

   p0_rq2_t p0_rq2;
   p0_rq_t p0_rq;
   p0_rs_t p0_rs;

   always_comb begin
      p0_rq2.addr = 16'hcafe;
      p0_rq.addr = 16'hbeef;
      p0_rs.data = 8'h5a;
   end

   initial begin
      #1;
      if(p0_rq2.addr != 16'hcafe) $stop;
      if(p0_rq.addr != 16'hbeef) $stop;
      if(p0_rs.data != 8'h5a) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
