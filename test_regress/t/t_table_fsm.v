// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;
   reg          reset;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire                 myevent;                // From test of Test.v
   wire                 myevent_pending;        // From test of Test.v
   wire [1:0]           state;                  // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .state                    (state[1:0]),
              .myevent                  (myevent),
              .myevent_pending          (myevent_pending),
              // Inputs
              .clk                      (clk),
              .reset                    (reset));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, myevent_pending,myevent,state};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x me=%0x mep=%x\n", $time, cyc, crc, result, myevent, myevent_pending);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      reset <= (cyc<2);
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h4e93a74bd97b25ef
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   state, myevent, myevent_pending,
   // Inputs
   clk, reset
   );
   input clk;
   input reset;
   output [1:0] state;
   output       myevent;
   output       myevent_pending;

   reg [5:0]    count = 0;
   always @ (posedge clk)
     if (reset) count <= 0;
     else count <= count + 1;

   reg          myevent = 1'b0;
   always @ (posedge clk)
     myevent <= (count == 6'd27);

   reg          myevent_done;
   reg          hickup_ready;
   reg          hickup_done;

   localparam STATE_ZERO   = 0;
   localparam STATE_ONE    = 1;
   localparam STATE_TWO    = 2;

   reg [1:0]    state                   = STATE_ZERO;
   reg          state_start_myevent     = 1'b0;
   reg          state_start_hickup      = 1'b0;
   reg          myevent_pending         = 1'b0;
   always @ (posedge clk) begin
      state <= state;
      myevent_pending <= myevent_pending || myevent;
      state_start_myevent <= 1'b0;
      state_start_hickup <= 1'b0;
      case (state)
        STATE_ZERO:
          if (myevent_pending) begin
             state <= STATE_ONE;
             myevent_pending <= 1'b0;
             state_start_myevent <= 1'b1;
          end else if (hickup_ready) begin
             state <= STATE_TWO;
             state_start_hickup <= 1'b1;
          end

        STATE_ONE:
          if (myevent_done)
            state <= STATE_ZERO;

        STATE_TWO:
          if (hickup_done)
            state <= STATE_ZERO;

        default:
          ; /* do nothing */
      endcase
   end

   reg [3:0] myevent_count = 0;
   always @ (posedge clk)
     if (state_start_myevent)
       myevent_count <= 9;
     else if (myevent_count > 0)
       myevent_count <= myevent_count - 1;

   initial myevent_done = 1'b0;
   always @ (posedge clk)
     myevent_done <= (myevent_count == 0);

   reg [4:0] hickup_backlog = 2;
   always @ (posedge clk)
     if (state_start_myevent)
       hickup_backlog <= hickup_backlog - 1;
     else if (state_start_hickup)
       hickup_backlog <= hickup_backlog + 1;

   initial hickup_ready = 1'b1;
   always @ (posedge clk)
     hickup_ready <= (hickup_backlog < 3);

   reg [3:0] hickup_count = 0;
   always @ (posedge clk)
     if (state_start_hickup)
       hickup_count <= 10;
     else if (hickup_count > 0)
       hickup_count <= hickup_count - 1;

   initial hickup_done = 1'b0;
   always @ (posedge clk)
     hickup_done <= (hickup_count == 1);

endmodule
