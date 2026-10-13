// DESCRIPTION: Verilator: Package names are separate from $unit declarations
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 3.13: Package and compilation-unit scope name spaces are distinct.

package mem_agent;
  class mem_agent #(type CONFIG = int);
    CONFIG cfg;
  endclass
endpackage

import mem_agent::*;

class derived extends mem_agent #();
endclass

package explicit_agent;
  class explicit_agent;
  endclass
endpackage

import explicit_agent::explicit_agent;

module t;
  // The wildcard import makes the class visible in the enclosing scope (IEEE 1800-2023 26.3).
  mem_agent #(byte) agent;
  explicit_agent explicit_agent_obj;
endmodule
