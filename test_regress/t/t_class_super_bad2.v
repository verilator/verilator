// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Rafal Kapuscik
// SPDX-License-Identifier: CC0-1.0
//

class Cls;
   task t;
      super.i = 1;  // Bad - no extends
   endtask
endclass
