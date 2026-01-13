//----------------------------------------------------------------------
// Copyright 2012 Accellera Systems Initiative
// Copyright 2015 Analog Devices, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2014 Cisco Systems, Inc.
// Copyright 2022-2023 Intel Corporation
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2014-2024 NVIDIA Corporation
// Copyright 2010 Synopsys, Inc.
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

// TITLE -- NODOCS -- UVM HDL Backdoor Access support routines.
//
// These routines provide an interface to the DPI/PLI
// implementation of backdoor access used by registers.
//
// If you DON'T want to use the DPI HDL API, then compile your
// SystemVerilog code with the vlog switch
//:   vlog ... +define+UVM_HDL_NO_DPI ...
//


`ifndef UVM_HDL__SVH
`define UVM_HDL__SVH


`ifndef UVM_HDL_MAX_WIDTH
`define UVM_HDL_MAX_WIDTH 1024
`endif

/* 
 * VARIABLE -- NODOCS -- UVM_HDL_MAX_WIDTH
 * Sets the maximum size bit vector for backdoor access. 
 * This parameter will be looked up by the 
 * DPI-C code using:
 *   vpi_handle_by_name(
 *     "uvm_pkg::UVM_HDL_MAX_WIDTH", 0);
 */

// @uvm-ieee 1800.2-2020 manual 19.6.1
parameter int UVM_HDL_MAX_WIDTH = `UVM_HDL_MAX_WIDTH;


typedef logic [UVM_HDL_MAX_WIDTH-1:0] uvm_hdl_data_t;

                            
`ifndef UVM_HDL_NO_DPI

  // Function -- NODOCS -- uvm_hdl_check_path
  //
  // Checks that the given HDL ~path~ exists. Returns 0 if NOT found, 1 otherwise.
  //
  import "DPI-C" context function int uvm_hdl_check_path(string path);


  // Function -- NODOCS -- uvm_hdl_deposit
  //
  // Sets the given HDL ~path~ to the specified ~value~.
  // Returns 1 if the call succeeded, 0 otherwise.
  //
  import "DPI-C" context function int uvm_hdl_deposit(string path, uvm_hdl_data_t value);


  // Function -- NODOCS -- uvm_hdl_force
  //
  // Forces the ~value~ on the given ~path~. Returns 1 if the call succeeded, 0 otherwise.
  //
  import "DPI-C" context function int uvm_hdl_force(string path, uvm_hdl_data_t value);


  // Function -- NODOCS -- uvm_hdl_force_time
  //
  // Forces the ~value~ on the given ~path~ for the specified amount of ~force_time~.
  // If ~force_time~ is 0, <uvm_hdl_deposit> is called.
  // Returns 1 if the call succeeded, 0 otherwise.
  //
  task uvm_hdl_force_time(string path, uvm_hdl_data_t value, time force_time = 0);
    if (force_time == 0) begin
      void'(uvm_hdl_deposit(path, value));
      return;
    end
    if (!uvm_hdl_force(path, value)) begin
      
      return;
    end

    #force_time;
    void'(uvm_hdl_release_and_read(path, value));
  endtask


  // Function -- NODOCS -- uvm_hdl_release_and_read
  //
  // Releases a value previously set with <uvm_hdl_force>.
  // Returns 1 if the call succeeded, 0 otherwise. ~value~ is set to
  // the HDL value after the release. For 'reg', the value will still be
  // the forced value until it has been procedurally reassigned. For 'wire',
  // the value will change immediately to the resolved value of its
  // continuous drivers, if any. If none, its value remains as forced until
  // the next direct assignment.
  //
  import "DPI-C" context function int uvm_hdl_release_and_read(string path, inout uvm_hdl_data_t value);


  // Function -- NODOCS -- uvm_hdl_release
  //
  // Releases a value previously set with <uvm_hdl_force>.
  // Returns 1 if the call succeeded, 0 otherwise.
  //
  import "DPI-C" context function int uvm_hdl_release(string path);


  // Function -- NODOCS -- uvm_hdl_read()
  //
  // Gets the value at the given ~path~.
  // Returns 1 if the call succeeded, 0 otherwise.
  //
  import "DPI-C" context function int uvm_hdl_read(string path, output uvm_hdl_data_t value);

`else

  function int uvm_hdl_check_path(string path);
    uvm_report_fatal("UVM_HDL_CHECK_PATH", 
      $sformatf("uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_HDL_NO_DPI"));
    return 0;
  endfunction

  function int uvm_hdl_deposit(string path, uvm_hdl_data_t value);
    uvm_report_fatal("UVM_HDL_DEPOSIT", 
      $sformatf("uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_HDL_NO_DPI"));
    return 0;
  endfunction

  function int uvm_hdl_force(string path, uvm_hdl_data_t value);
    uvm_report_fatal("UVM_HDL_FORCE", 
      $sformatf("uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_HDL_NO_DPI"));
    return 0;
  endfunction

  task uvm_hdl_force_time(string path, uvm_hdl_data_t value, time force_time=0);
    uvm_report_fatal("UVM_HDL_FORCE_TIME", 
      $sformatf("uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_HDL_NO_DPI"));
  endtask

  function int uvm_hdl_release(string path);
    uvm_report_fatal("UVM_HDL_RELEASE", 
      $sformatf("uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_HDL_NO_DPI"));
    return 0;
  endfunction

  function int uvm_hdl_read(string path, output uvm_hdl_data_t value);
    uvm_report_fatal("UVM_HDL_READ", 
      $sformatf("uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_HDL_NO_DPI"));
    return 0;
  endfunction

`endif

`endif
