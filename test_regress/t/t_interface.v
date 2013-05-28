// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic   rst = 1'b1;  // reset
   integer rst_cnt = 0;

   // reset is removed after a delay
   always @ (posedge clk)
   begin
      rst_cnt <= rst_cnt + 1;
      rst     <= rst_cnt <= 3;
   end

   // counters
   int cnt;
   int cnt_src;
   int cnt_drn;

   // add all counters
   assign cnt = cnt_src + cnt_drn + inf.cnt;

   // finish report
   always @ (posedge clk)
   if (cnt == 3*16) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   // interface instance
   handshake inf (
      .clk (clk),
      .rst (rst)
   );

   // source instance
   source #(
      .RW  (8),
      .RP  (8'b11100001)
   ) source (
      .clk  (clk),
      .rst  (rst),
      .inf  (inf),
      .cnt  (cnt_src)
   );

   // drain instance
   drain #(
      .RW  (8),
      .RP  (8'b11010100)
   ) drain (
      .clk  (clk),
      .rst  (rst),
      .inf  (inf),
      .cnt  (cnt_drn)
   );

endmodule : t


// interface definition
interface handshake #(
   parameter int unsigned WC = 32
)(
   input logic clk,
   input logic rst
);

   // modport signals
   logic req;  // request
   logic grt;  // grant
   logic inc;  // increment

   // local signals
   integer cnt;  // counter

   // source
   modport src (
      output req,
      input  grt
   );

   // drain
   modport drn (
      input  req,
      output grt
   );

   // incremet condition
   assign inc = req & grt;

   // local logic (counter)
   always @ (posedge clk, posedge rst)
   if (rst) cnt <= '0;
   else     cnt <= cnt + {31'h0, inc};

endinterface : handshake


// source module
module source #(
   // random generator parameters
   parameter int unsigned RW=1,   // LFSR width
   parameter bit [RW-1:0] RP='0,  // LFSR polinom
   parameter bit [RW-1:0] RR='1   // LFSR reset state
)(
   input logic    clk,
   input logic    rst,
   handshake.src  inf,
   output integer cnt
);

   // LFSR
   logic [RW-1:0] rnd;

   // LFSR in Galois form
   always @ (posedge clk, posedge rst)
   if (rst) rnd <= RR;
   else     rnd <= {rnd[0], rnd[RW-1:1]} ^ ({RW{rnd[0]}} & RP);

   // counter
   always @ (posedge clk, posedge rst)
   if (rst) cnt <= 32'd0;
   else     cnt <= cnt + {31'd0, (inf.req & inf.grt)};

   // request signal
   assign inf.req = rnd[0];

endmodule : source


// drain module
module drain #(
   // random generator parameters
   parameter int unsigned RW=1,   // LFSR width
   parameter bit [RW-1:0] RP='0,  // LFSR polinom
   parameter bit [RW-1:0] RR='1   // LFSR reset state
)(
   input logic    clk,
   input logic    rst,
   handshake.drn  inf,
   output integer cnt
);

   // LFSR
   logic [RW-1:0] rnd;

   // LFSR in Galois form
   always @ (posedge clk, posedge rst)
   if (rst) rnd <= RR;
   else     rnd <= {rnd[0], rnd[RW-1:1]} ^ ({RW{rnd[0]}} & RP);

   // counter
   always @ (posedge clk, posedge rst)
   if (rst) cnt <= 32'd0;
   else     cnt <= cnt + {31'd0, (inf.req & inf.grt)};

   // grant signal
   assign inf.grt = rnd[0];

endmodule : drain
