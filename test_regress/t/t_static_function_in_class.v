// DESCRIPTION: Verilator: Simple static elaboration case
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

class string_utils;
  typedef string array_of_string[];

  static function array_of_string split_by_dash(string s);
    string 	  parts[$];
    int 	  last_char_position = -1;
    for (int i = 0; i < s.len(); i++) begin
      if (i == s.len()-1) begin
        parts.push_back(s.substr(last_char_position+1, i));
      end
      // Can't remove this, because then the code will work
      if (string'(s[i]) == "-") begin
        parts.push_back(s.substr(last_char_position+1, i-1));
        last_char_position = i;
      end
    end // for (int i = 0; i < s.len(); i++)
    return parts;
  endfunction // split_by_dash
endclass // string_utils

class filter;
  local static filter single_instance;

  static function filter get();
    if (single_instance == null)
      single_instance = new();
    return single_instance;
  endfunction // get

  local function new();
    string parts[] = string_utils::split_by_dash("*");
    if (parts.size() != 1)
      $fatal(0, "Expected single element");
    if (parts[0] != "*")
      $fatal(0, "Expected element to be *");
   endfunction // new
endclass // filter

module t (/*AUTOARG*/);
  const filter _filter = filter::get();
  initial begin
    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
