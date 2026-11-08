// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A cast is not a variable, so it cannot be assigned (IEEE 1800-2023 11.4.14.3, A.8.5)

module t;

  typedef byte bytes_t[4];

  task automatic tk(output logic [14:0] o);
    o = 15'h0;
  endtask

  function automatic int fo(output logic [14:0] o);
    o = 15'h0;
    return 0;
  endfunction

  initial begin
    int i;
    logic [14:0] v15;
    {<<8{bytes_t'(i)}} = i;  // Bad: a cast, in a stream target
    {<<8{i, bytes_t'(i)}} = {i, i};  // Bad: also concatenated
    {>>{int'(i)}} = i;  // Bad: also to a packed type
    {>>{15'(v15)}} = v15;  // Bad: also a size cast
    tk(15'(v15));  // Bad: also as an output argument
    i = {>>{fo(15'(v15))}};  // Bad: also in a stream, but not its target
  end

endmodule
