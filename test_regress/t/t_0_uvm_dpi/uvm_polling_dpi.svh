//----------------------------------------------------------------------
// Copyright 2023 Intel Corporation
// Copyright 2023 NVIDIA Corporation
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

`ifndef UVM_DPI_POLLING_SVH
`define UVM_DPI_POLLING_SVH
`ifndef UVM_NO_DPI
  import "DPI-C" context function chandle uvm_polling_create(input string name, input int sv_key);

   // Set/get value-change callback enable on the chosen signal.
   import "DPI-C" context function void uvm_polling_set_enable_callback(chandle hnd, int enable);
   import "DPI-C" context function int uvm_polling_get_callback_enable(chandle hnd);

   // Get the signal's value.

   // Get the signal's static properties.
   import "DPI-C" context function int uvm_polling_setup_notifier(string fullname);
   import "DPI-C" context function void uvm_polling_process_changelist();

   import "DPI-C" context function int uvm_hdl_signal_size(string path);
   // import "DPI-C" context function void uvm_polling_free_mem_structures();


`else 
  // uvm_polling_create
  function chandle uvm_polling_create(input string name, input int sv_key);
   chandle ch;
    uvm_report_fatal("UVM_HDL_POLLING",
      $sformatf("VPI access is disabled. Recompile without +define+UVM_HDL_NO_DPI"));
    return ch;
  endfunction
  
   // uvm_polling_set_enable_callback
   function void uvm_polling_set_enable_callback(chandle hnd, int enable);
    uvm_report_fatal("UVM_HDL_POLLING",
      $sformatf("VPI access is disabled. Recompile without +define+UVM_HDL_NO_DPI"));
  endfunction

   // uvm_polling_get_callback_enable
   function int uvm_polling_get_callback_enable(chandle hnd);
    uvm_report_fatal("UVM_HDL_POLLING",
      $sformatf("VPI access is disabled. Recompile without +define+UVM_HDL_NO_DPI"));
    endfunction


  // uvm_polling_setup_notifier
   function int uvm_polling_setup_notifier(string fullname);
    uvm_report_fatal("UVM_HDL_POLLING",
      $sformatf("VPI access is disabled. Recompile without +define+UVM_HDL_NO_DPI"));
	
   endfunction

 // uvm_polling_process_changelist
   function void uvm_polling_process_changelist();
    uvm_report_fatal("UVM_HDL_POLLING",
      $sformatf("VPI access is disabled. Recompile without +define+UVM_HDL_NO_DPI"));
  endfunction




	function int uvm_hdl_signal_size(string path);
    		uvm_report_fatal("UVM_HDL_POLLING",
      			$sformatf("VPI access is disabled. Recompile without +define+UVM_HDL_NO_DPI"));
	endfunction

`endif

`endif
