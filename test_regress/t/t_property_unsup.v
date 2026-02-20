// SPDX-FileCopyrightText: 2001-2020 Daniel Kroening, Edmund Clarke
// SPDX-License-Identifier: BSD-3-Clause
//
// (C) 2001-2020, Daniel Kroening, Edmund Clarke,
// Computer Science Department, University of Oxford
// Computer Science Department, Carnegie Mellon University
//
// All rights reserved. Redistribution and use in source and binary forms, with
// or without modification, are permitted provided that the following
// conditions are met:
//
//   1. Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//
//   2. Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//
//   3. Neither the name of the University nor the names of its contributors
//      may be used to endorse or promote products derived from this software
//      without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.
//
// You can contact the author at:
//   - homepage : https://www.cprover.org/ebmc/
//   - source repository : https://github.com/diffblue/hw-cbmc

module t (  /*AUTOARG*/
    // Inputs
    clk,
    reset
);
  input clk;
  input reset;
  eventually1 eventually1 (.*);
  eventually2 eventually2 (.*);
  sva_implies2 sva_implies2 (.*);
  sva_iff2 sva_iff2 (.*);
endmodule

module eventually1 (
    input clk,
    input reset
);

  // count up from 0 to 10
  reg [7:0] counter;
  initial counter = 0;

  always @(posedge clk) if (counter != 10) counter = counter + 1;

  // expected to pass
  p0 :
  assert property (counter == 1 implies eventually[1: 2] counter == 3);

endmodule

module eventually2 (
    input clk,
    input reset
);

  reg [7:0] counter;
  initial counter = 0;
  always @(posedge clk) counter = 0;

  // expected to fail
  p0 :
  assert property (eventually[0: 2] counter == 3);

endmodule

module sva_implies2 (
    input a,
    b
);

  p0 :
  assert property ((always a) implies (always a));
  p1 :
  assert property ((a or(always b)) implies (a or(always b)));
  p2 :
  assert property ((eventually[0: 1] a) implies (eventually[0: 1] a));
  p3 :
  assert property ((s_eventually a) implies (s_eventually a));
  p4 :
  assert property ((a until b) implies (a until b));
  p5 :
  assert property ((a s_until b) implies (a s_until b));
  p6 :
  assert property ((a until_with b) implies (a until_with b));
  p7 :
  assert property ((a s_until_with b) implies (a s_until_with b));
  p8 :
  assert property ((a |-> b) implies (a |-> b));
  p9 :
  assert property ((a #-# b) implies (a #-# b));

endmodule

module sva_iff2 (
    input a,
    b
);

  p0 :
  assert property ((always a) iff (always a));
  p1 :
  assert property ((eventually[0: 1] a) iff (eventually[0: 1] a));
  p2 :
  assert property ((s_eventually a) iff (s_eventually a));
  p3 :
  assert property ((a until b) iff (a until b));
  p4 :
  assert property ((a s_until b) iff (a s_until b));
  p5 :
  assert property ((a until_with b) iff (a until_with b));
  p6 :
  assert property ((a s_until_with b) iff (a s_until_with b));
  p7 :
  assert property ((a |-> b) iff (a |-> b));
  p8 :
  assert property ((a #-# b) iff (a #-# b));

endmodule
