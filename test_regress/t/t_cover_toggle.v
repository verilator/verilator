// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {logic a;} str_logic;

module t (/*AUTOARG*/
   // Inputs
   clk, check_real, check_array_real, check_string
   );

   input clk;
   input real check_real; // Check issue #2741
   input real check_array_real [1:0];
   input string check_string; // Check issue #2766

   typedef struct packed {
      union packed {
         logic    ua;
         logic    ub;
      } u;
      logic b;
   } str_t;

   reg   toggle; initial toggle='0;

   str_t stoggle; initial stoggle='0;

   str_logic strl; initial strl='0;

   union {
      real val1;  // TODO use bit [7:0] here
      real val2;  // TODO use bit [3:0] here
   } utoggle;

   const reg aconst = '0;

   reg [1:0][1:0] ptoggle; initial ptoggle=0;

   integer cyc; initial cyc=1;
   wire [7:0] cyc_copy = cyc[7:0];
   wire       toggle_up;

   typedef struct {
      int q[$];
   } str_queue_t;
   str_queue_t str_queue;

   assign strl.a = clk;

   alpha a1 (/*AUTOINST*/
             // Outputs
             .toggle_up                 (toggle_up),
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle),
             .cyc_copy                  (cyc_copy[7:0]));
   alpha a2 (/*AUTOINST*/
             // Outputs
             .toggle_up                 (toggle_up),
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle),
             .cyc_copy                  (cyc_copy[7:0]));

   beta  b1 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle_up                 (toggle_up));

   off   o1 (/*AUTOINST*/
             // Inputs
             .clk                       (clk),
             .toggle                    (toggle));

   param#(1) p1 (/*AUTOINST*/
                 // Inputs
                 .clk                   (clk),
                 .toggle                (toggle));

   param#() p2 (/*AUTOINST*/
                // Inputs
                .clk                    (clk),
                .toggle                 (toggle));

   mod_struct i_mod_struct (/*AUTOINST*/
                            // Inputs
                            .input_struct   (strl));


   reg [1:0]  memory[121:110];

   wire [1023:0] largeish = {992'h0, cyc};
   // CHECK_COVER_MISSING(-1)

   always @ (posedge clk) begin
      if (cyc != 0) begin
         cyc <= cyc + 1;
         memory[cyc + 'd100] <= memory[cyc + 'd100] + 2'b1;
         toggle <= '0;
         stoggle.u <= toggle;
         stoggle.b <= toggle;
         utoggle.val1 <= real'(cyc[7:0]);
         ptoggle[0][0] <= toggle;
         if (cyc == 3) begin
            str_queue.q.push_back(1);
            toggle <= '1;
         end
         if (cyc == 4) begin
            if (str_queue.q.size() != 1) $stop;
            toggle <= '0;
         end
         else if (cyc == 10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module alpha (/*AUTOARG*/
   // Outputs
   toggle_up,
   // Inputs
   clk, toggle, cyc_copy
   );

   // t.a1 and t.a2 collapse to a count of 2

   input clk;

   input toggle;
   // CHECK_COVER(-1,"top.t.a*",4)
   // 2 edges * (t.a1 and t.a2)

   input [7:0] cyc_copy;
   // CHECK_COVER(-1,"top.t.a*","cyc_copy[0]",22)
   // CHECK_COVER(-2,"top.t.a*","cyc_copy[1]",10)
   // CHECK_COVER(-3,"top.t.a*","cyc_copy[2]",4)
   // CHECK_COVER(-4,"top.t.a*","cyc_copy[3]",2)
   // CHECK_COVER(-5,"top.t.a*","cyc_copy[4]",0)
   // CHECK_COVER(-6,"top.t.a*","cyc_copy[5]",0)
   // CHECK_COVER(-7,"top.t.a*","cyc_copy[6]",0)
   // CHECK_COVER(-8,"top.t.a*","cyc_copy[7]",0)

   reg         toggle_internal;
   // CHECK_COVER(-1,"top.t.a*",4)
   // 2 edges * (t.a1 and t.a2)

   output reg  toggle_up;
   // CHECK_COVER(-1,"top.t.a*",4)
   // 2 edges * (t.a1 and t.a2)

   always @ (posedge clk) begin
      toggle_internal <= toggle;
      toggle_up       <= toggle;
   end
endmodule

module beta (/*AUTOARG*/
   // Inputs
   clk, toggle_up
   );

   input clk;

   input toggle_up;
   // CHECK_COVER(-1,"top.t.b1","toggle_up",2)

   /* verilator public_module */

   always @ (posedge clk) begin
      if (0 && toggle_up) begin end
   end
endmodule

module off (/*AUTOARG*/
   // Inputs
   clk, toggle
   );

   // verilator coverage_off
   input clk;
   // CHECK_COVER_MISSING(-1)

   // verilator coverage_on
   input toggle;
   // CHECK_COVER(-1,"top.t.o1","toggle",2)

endmodule

module param #(parameter P = 2) (/*AUTOARG*/
   // Inputs
   clk, toggle
   );

   input clk;
   input toggle;

   logic z;

   for (genvar i = 0; i < P; i++) begin
      logic x;
      always @ (posedge clk) begin
         x <= toggle;
      end
      for (genvar j = 0; j < 3; j++) begin
         logic [2:0] y;
         always @ (negedge clk) begin
            y <= {toggle, ~toggle, 1'b1};
         end
      end
   end
   if (P > 1) begin : gen_1
      assign z = 1;
   end
endmodule

module mod_struct(/*AUTOARG*/
   // Inputs
   input_struct
   );

   input str_logic input_struct;
endmodule
