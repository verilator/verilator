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

module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // Starting from a particular state,
  // first_match yields the sequence that _ends_ first.

  // fails
  initial p0: assert property ((##1 1) or (##2 1) |-> x==1);

  // passes
  initial p1: assert property (first_match((##1 1) or (##2 1)) |-> x==1);

  // fails
  initial p2: assert property (1 or ##1 1 |-> x==0);

  // passes
  initial p3: assert property (first_match(1 or ##1 1) |-> x==0);

endmodule
