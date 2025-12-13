//----------------------------------------------------------------------
// Copyright 2010-2012 Mentor Graphics Corporation
// Copyright 2010-2018 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------



`ifndef UVM_REGEX_NO_DPI
import "DPI-C" context function int uvm_re_match(string re, string str);
import "DPI-C" context function string uvm_glob_to_re(string glob);

`else

// The Verilog only version does not match regular expressions,
// it only does glob style matching.
function int uvm_re_match(string re, string str);
  int e, es, s, ss;
  string tmp;
  e  = 0; s  = 0;
  es = 0; ss = 0;

  if(re.len() == 0)
    return 0;

  // The ^ used to be used to remove the implicit wildcard, but now we don't
  // use implicit wildcard so this character is just stripped.
  if(re[0] == "^")
    re = re.substr(1, re.len()-1);

  //This loop is only needed when the first character of the re may not
  //be a *.
  while (s != str.len() && re.getc(e) != "*") begin
    if ((re.getc(e) != str.getc(s)) && (re.getc(e) != "?"))
      return 1;
    e++; s++;
  end

  while (s != str.len()) begin
    if (re.getc(e) == "*") begin
      e++;
      if (e == re.len()) begin
        return 0;
      end
      es = e;
      ss = s+1;
    end
    else if (re.getc(e) == str.getc(s) || re.getc(e) == "?") begin
      e++;
      s++;
    end
    else begin
      e = es;
      s = ss++;
    end
  end
  while (e < re.len() && re.getc(e) == "*")
    e++;
  if(e == re.len()) begin
    return 0;
  end
  else begin
    return 1;
  end
endfunction

function string uvm_glob_to_re(string glob);
  return glob;
endfunction

`endif
