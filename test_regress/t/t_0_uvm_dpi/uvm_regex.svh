//----------------------------------------------------------------------
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 Mentor Graphics Corporation
// Copyright 2020-2024 NVIDIA Corporation
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

//----------------------------------------------------------------------
// Git details (see DEVELOPMENT.md):
//
// $File$
// $Rev$
// $Hash$
//
//----------------------------------------------------------------------




`ifndef UVM_REGEX_NO_DPI
import "DPI-C" function string uvm_re_deglobbed(string glob, bit with_brackets);
import "DPI-C" function string uvm_re_buffer();
import "DPI-C" function void uvm_re_free(chandle rexp);
import "DPI-C" function chandle uvm_re_comp(string re, bit deglob);
import "DPI-C" function int uvm_re_exec(chandle rexp, string str);
import "DPI-C" function chandle uvm_re_compexec(string re, string str, bit deglob, output int exec_ret);
import "DPI-C" function bit uvm_re_compexecfree(string re, string str, bit deglob, output int exec_ret);

typedef class uvm_regex_cache;

// The uvm_re_match cache is disabled by default, to avoid 
// potential issues with save-and-restore causing illegal c-side 
// dereferencing.  When enabled, uvm_re_match should be significantly 
// faster.   
`ifdef UVM_ENABLE_RE_MATCH_CACHE
function int uvm_re_match(string re, string str, bit deglob = 0);
  uvm_regex_cache cache;
  chandle cached[$];
  int retval;
  
  cache = uvm_regex_cache::get_inst();
  cached = cache.get(re);
  if (cached.size()) begin
    // Cache hit, use pre-compiled regex
    retval = uvm_re_exec(cached[0], str);
  end
  else begin
    // Cache miss, compile and cache regex
    chandle rexp;
    rexp = uvm_re_compexec(re, str, deglob, retval);
    if (rexp == null) begin
      uvm_report_error("UVM/DPI/REGEX", uvm_re_buffer());
    end
    else begin
      cache.put(re, rexp);
    end
  end // else: !if(cached.size())
  return retval;
endfunction : uvm_re_match

`else // !`ifdef UVM_ENABLE_RE_MATCH_CACHE

function int uvm_re_match(string re, string str, bit deglob = 0);
  int retval;
  bit success;
  success = uvm_re_compexecfree(re, str, deglob, retval);
  if (!success) begin
    uvm_report_error("UVM/DPI/REGEX", uvm_re_buffer());
  end
  return retval;
endfunction : uvm_re_match

`endif // !`ifdef UVM_ENABLE_RE_MATCH_CACHE


function string uvm_glob_to_re(string glob);
  return uvm_re_deglobbed(glob, 1);
endfunction : uvm_glob_to_re

`else

// The Verilog only version does not match regular expressions,
// it only does glob style matching.
// NOTE: The deglob argument is unused in Verilog only mode,
// as it doesn't make any sense.
function int uvm_re_match(string re, string str, bit deglob = 0);
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
