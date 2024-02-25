// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef string array_of_string_t[];

   typedef struct {
      string positive;
      string negative;
   } filter_expression_parts_t;

   function automatic array_of_string_t split_by_char(string c, string s);
      string parts[$];
      int    last_char_position = -1;

      for (int i = 0; i < s.len(); i++) begin
         if (i == s.len()-1)
           parts.push_back(s.substr(last_char_position+1, i));
         if (string'(s[i]) == c) begin
            parts.push_back(s.substr(last_char_position+1, i-1));
            last_char_position = i;
         end
      end

      $display("%p", parts);
      return parts;
   endfunction

   function filter_expression_parts_t get_filter_expression_parts(string raw_filter);
      string parts[];
      parts = split_by_char("-", raw_filter);
      return '{ parts[0], parts[1] };
   endfunction

   initial begin
      string raw_filter = "parta-partb";
      filter_expression_parts_t parts = get_filter_expression_parts(raw_filter);
      $display("%p", parts);
      if (parts.positive != "parta") $stop;
      if (parts.negative != "partb") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
