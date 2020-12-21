//-------------------------------------------------------------------------
// This Verilog file was developed by Altera Corporation.  It may be
// freely copied and/or distributed at no cost.  Any persons using this
// file for any purpose do so at their own risk, and are responsible for
// the results of such use.  Altera Corporation does not guarantee that
// this file is complete, correct, or fit for any particular purpose.
// NO WARRANTY OF ANY KIND IS EXPRESSED OR IMPLIED.  This notice must
// accompany any copy of this file.
//------------------------------------------------------------------------
//
// Quartus Prime 16.1.0 Build 196 10/24/2016
//
//------------------------------------------------------------------------
// LPM Synthesizable Models (Support string type generic)
// These models are based on LPM version 220 (EIA-IS103 October 1998).
//------------------------------------------------------------------------
//
//-----------------------------------------------------------------------------
// Assumptions:
//
// 1. The default value for LPM_SVALUE, LPM_AVALUE, LPM_PVALUE, and
//    LPM_STRENGTH is string UNUSED.
//
//-----------------------------------------------------------------------------
// Verilog Language Issues:
//
// Two dimensional ports are not supported. Modules with two dimensional
// ports are implemented as one dimensional signal of (LPM_SIZE * LPM_WIDTH)
// bits wide.
//
//-----------------------------------------------------------------------------
//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  LPM_MEMORY_INITIALIZATION
//
// Description     :  Common function to read intel-hex format data file with
//                    extension .hex and creates the equivalent verilog format
//                    data file with extension .ver.
//
// Limitation      :  Supports only record type '00'(data record), '01'(end of
//                     file record) and '02'(extended segment address record).
//
// Results expected:  Creates the verilog format data file with extension .ver
//                     and return the name of the file.
//
//END_MODULE_NAME--------------------------------------------------------------

//See also: https://github.com/twosigma/verilator_support
// verilator lint_off COMBDLY
// verilator lint_off INITIALDLY
// verilator lint_off MULTIDRIVEN
// verilator lint_off UNSIGNED
// verilator lint_off WIDTH
// verilator lint_off LATCH

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

`define LPM_TRUE 1
`define LPM_FALSE 0
`define LPM_NULL 0
`define LPM_EOF -1
`define LPM_MAX_NAME_SZ     128
`define LPM_MAX_WIDTH       256
`define LPM_COLON           ":"
`define LPM_DOT             "."
`define LPM_NEWLINE         "\n"
`define LPM_CARRIAGE_RETURN  8'h0D
`define LPM_SPACE           " "
`define LPM_TAB             "\t"
`define LPM_OPEN_BRACKET    "["
`define LPM_CLOSE_BRACKET   "]"
`define LPM_OFFSET          9
`define LPM_H10             8'h10
`define LPM_H10000          20'h10000
`define LPM_AWORD           8
`define LPM_MASK15          32'h000000FF
`define LPM_EXT_STR         "ver"
`define LPM_PERCENT         "%"
`define LPM_MINUS           "-"
`define LPM_SEMICOLON       ";"
`define LPM_EQUAL           "="

// MODULE DECLARATION
module LPM_MEMORY_INITIALIZATION;

/****************************************************************/
/* convert uppercase character values to lowercase.             */
/****************************************************************/
function [8:1] tolower;
    input [8:1] given_character;
    reg [8:1] conv_char;

begin
    if ((given_character >= 65) && (given_character <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
    begin
        conv_char = given_character + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
        tolower = conv_char;
    end
    else
        tolower = given_character;
end
endfunction

/****************************************************************/
/* Read in Altera-mif format data to verilog format data.       */
/****************************************************************/
task convert_mif2ver;
    input[`LPM_MAX_NAME_SZ*8 : 1] in_file;
    input width;
    output [`LPM_MAX_NAME_SZ*8 : 1] out_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] in_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] out_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] buffer;
    reg [`LPM_MAX_WIDTH : 0] memory_data1, memory_data2;
    reg [8 : 1] c;
    reg [3 : 0] hex, tmp_char;
    reg [24 : 1] address_radix, data_radix;
    reg get_width;
    reg get_depth;
    reg get_data_radix;
    reg get_address_radix;
    reg width_found;
    reg depth_found;
    reg data_radix_found;
    reg address_radix_found;
    reg get_address_data_pairs;
    reg get_address;
    reg get_data;
    reg display_address;
    reg invalid_address;
    reg get_start_address;
    reg get_end_address;
    reg done;
    reg error_status;
    reg first_rec;
    reg last_rec;

    integer width;
    integer memory_width, memory_depth;
    integer value;
    integer ifp, ofp, r, r2;
    integer i, j, k, m, n;

    integer off_addr, nn, address, tt, cc, aah, aal, dd, sum ;
    integer start_address, end_address;
    integer line_no;
    integer character_count;
    integer comment_with_percent_found;
    integer comment_with_double_minus_found;

begin
        done = `LPM_FALSE;
        error_status = `LPM_FALSE;
        first_rec = `LPM_FALSE;
        last_rec = `LPM_FALSE;
        comment_with_percent_found = `LPM_FALSE;
        comment_with_double_minus_found = `LPM_FALSE;

        off_addr= 0;
        nn= 0;
        address = 0;
        start_address = 0;
        end_address = 0;
        tt= 0;
        cc= 0;
        aah= 0;
        aal= 0;
        dd= 0;
        sum = 0;
        line_no = 1;
        c = 0;
        hex = 0;
        value = 0;
        buffer = "";
        character_count = 0;
        memory_width = 0;
        memory_depth = 0;
        memory_data1 = {(`LPM_MAX_WIDTH+1) {1'b0}};
        memory_data2 = {(`LPM_MAX_WIDTH+1) {1'b0}};
        address_radix = "hex";
        data_radix = "hex";
        get_width = `LPM_FALSE;
        get_depth = `LPM_FALSE;
        get_data_radix = `LPM_FALSE;
        get_address_radix = `LPM_FALSE;
        width_found = `LPM_FALSE;
        depth_found = `LPM_FALSE;
        data_radix_found = `LPM_FALSE;
        address_radix_found = `LPM_FALSE;
        get_address_data_pairs = `LPM_FALSE;
        display_address = `LPM_FALSE;
        invalid_address = `LPM_FALSE;
        get_start_address = `LPM_FALSE;
        get_end_address = `LPM_FALSE;

        if((in_file[4*8 : 1] == ".dat") || (in_file[4*8 : 1] == ".DAT"))
            out_file = in_file;
        else
        begin
            ifp = $fopen(in_file, "r");

            if (ifp == `LPM_NULL)
            begin
                $display("ERROR: cannot read %0s.", in_file);
                $display("Time: %0t  Instance: %m", $time);
                done = `LPM_TRUE;
            end

            out_file = in_file;

            if((out_file[4*8 : 1] == ".mif") || (out_file[4*8 : 1] == ".MIF"))
                out_file[3*8 : 1] = `LPM_EXT_STR;
            else
            begin
                $display("ERROR: Invalid input file name %0s. Expecting file with .mif extension and Altera-mif data format.", in_file);
                $display("Time: %0t  Instance: %m", $time);
                done = `LPM_TRUE;
            end

            if (!done)
            begin
                ofp = $fopen(out_file, "w");

                if (ofp == `LPM_NULL)
                begin
                    $display("ERROR : cannot write %0s.", out_file);
                    $display("Time: %0t  Instance: %m", $time);
                    done = `LPM_TRUE;
                end
            end

            while((!done) && (!error_status))
            begin : READER

                r = $fgetc(ifp);

                if (r == `LPM_EOF)
                begin
                // to do : add more checking on whether a particular assigment(width, depth, memory/address) are mising
                    if(!first_rec)
                    begin
                        error_status = `LPM_TRUE;
                        $display("WARNING: %0s, Intel-hex data file is empty.", in_file);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else if (!get_address_data_pairs)
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Missing `content begin` statement.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                    else if(!last_rec)
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Missing `end` statement.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                    done = `LPM_TRUE;
                end
                else if ((r == `LPM_NEWLINE) || (r == `LPM_CARRIAGE_RETURN))
                begin
                    if ((buffer == "contentbegin") && (get_address_data_pairs == `LPM_FALSE))
                    begin
                        get_address_data_pairs = `LPM_TRUE;
                        get_address = `LPM_TRUE;
                        buffer = "";
                    end
                    else if (buffer == "content")
                    begin
                        // continue to next character
                    end
                    else
                    if (buffer != "")
                    begin
                        // found invalid syntax in the particular line.
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                        disable READER;
                    end
                    line_no = line_no +1;

                end
                else if ((r == `LPM_SPACE) || (r == `LPM_TAB))
                begin
                    // continue to next character;
                end
                else if (r == `LPM_PERCENT)
                begin
                    // Ignore all the characters which which is part of comment.
                    r = $fgetc(ifp);

                    while ((r != `LPM_PERCENT) && (r != `LPM_NEWLINE) && (r != `LPM_CARRIAGE_RETURN))
                    begin
                        r = $fgetc(ifp);
                    end

                    if ((r == `LPM_NEWLINE) || (r == `LPM_CARRIAGE_RETURN))
                    begin
                        line_no = line_no +1;

                        if ((buffer == "contentbegin") && (get_address_data_pairs == `LPM_FALSE))
                        begin
                            get_address_data_pairs = `LPM_TRUE;
                            get_address = `LPM_TRUE;
                            buffer = "";
                        end
                    end
                end
                else if (r == `LPM_MINUS)
                begin
                    r = $fgetc(ifp);
                    if (r == `LPM_MINUS)
                    begin
                        // Ignore all the characters which which is part of comment.
                        r = $fgetc(ifp);

                        while ((r != `LPM_NEWLINE) && (r != `LPM_CARRIAGE_RETURN))
                        begin
                            r = $fgetc(ifp);

                        end

                        if ((r == `LPM_NEWLINE) || (r == `LPM_CARRIAGE_RETURN))
                        begin
                            line_no = line_no +1;

                            if ((buffer == "contentbegin") && (get_address_data_pairs == `LPM_FALSE))
                            begin
                                get_address_data_pairs = `LPM_TRUE;
                                get_address = `LPM_TRUE;
                                buffer = "";
                            end
                        end
                    end
                    else
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                        done = `LPM_TRUE;
                        disable READER;
                    end
                end
                else if (r == `LPM_EQUAL)
                begin
                    if (buffer == "width")
                    begin
                        if (width_found == `LPM_FALSE)
                        begin
                            get_width = `LPM_TRUE;
                            buffer = "";
                        end
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Width has already been specified once.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                        end
                    end
                    else if (buffer == "depth")
                    begin
                        get_depth = `LPM_TRUE;
                        buffer = "";
                    end
                    else if (buffer == "data_radix")
                    begin
                        get_data_radix = `LPM_TRUE;
                        buffer = "";
                    end
                    else if (buffer == "address_radix")
                    begin
                        get_address_radix = `LPM_TRUE;
                        buffer = "";
                    end
                    else
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Unknown setting (%0s).", in_file, line_no, buffer);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (r == `LPM_COLON)
                begin
                    if (!get_address_data_pairs)
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Missing `content begin` statement.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                    else if (invalid_address == `LPM_TRUE)
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                    begin
                        get_address = `LPM_FALSE;
                        get_data = `LPM_TRUE;
                        display_address = `LPM_TRUE;
                    end
                end
                else if (r == `LPM_DOT)
                begin
                    r = $fgetc(ifp);
                    if (r == `LPM_DOT)
                    begin
                        if (get_start_address == `LPM_TRUE)
                        begin
                            start_address = address;
                            address = 0;
                            get_start_address = `LPM_FALSE;
                            get_end_address = `LPM_TRUE;
                        end
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end
                    end
                    else
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                        done = `LPM_TRUE;
                        disable READER;
                    end
                end
                else if (r == `LPM_OPEN_BRACKET)
                begin
                    get_start_address = `LPM_TRUE;
                end
                else if (r == `LPM_CLOSE_BRACKET)
                begin
                    if (get_end_address == `LPM_TRUE)
                    begin
                        end_address = address;
                        address = 0;
                        get_end_address = `LPM_FALSE;
                    end
                    else
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                        done = `LPM_TRUE;
                        disable READER;
                    end
                end
                else if (r == `LPM_SEMICOLON)
                begin
                    if (get_width == `LPM_TRUE)
                    begin
                        width_found = `LPM_TRUE;
                        memory_width = value;
                        value = 0;
                        get_width = `LPM_FALSE;
                    end
                    else if (get_depth == `LPM_TRUE)
                    begin
                        depth_found = `LPM_TRUE;
                        memory_depth = value;
                        value = 0;
                        get_depth = `LPM_FALSE;
                    end
                    else if (get_data_radix == `LPM_TRUE)
                    begin
                        data_radix_found = `LPM_TRUE;
                        get_data_radix = `LPM_FALSE;

                        if ((buffer == "bin") || (buffer == "oct") || (buffer == "dec") || (buffer == "uns") ||
                            (buffer == "hex"))
                        begin
                            data_radix = buffer[24 : 1];
                        end
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid assignment (%0s) to data_radix.", in_file, line_no, buffer);
                            $display("Time: %0t  Instance: %m", $time);
                        end
                        buffer = "";
                    end
                    else if (get_address_radix == `LPM_TRUE)
                    begin
                        address_radix_found = `LPM_TRUE;
                        get_address_radix = `LPM_FALSE;

                        if ((buffer == "bin") || (buffer == "oct") || (buffer == "dec") || (buffer == "uns") ||
                            (buffer == "hex"))
                        begin
                            address_radix = buffer[24 : 1];
                        end
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid assignment (%0s) to address radix.", in_file, line_no, buffer);
                            $display("Time: %0t  Instance: %m", $time);
                        end
                        buffer = "";
                    end
                    else if (buffer == "end")
                    begin
                        if (get_address_data_pairs == `LPM_TRUE)
                        begin
                            last_rec = `LPM_TRUE;
                            buffer = "";
                        end
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Missing `content begin` statement.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                        end
                    end
                    else if (get_data == `LPM_TRUE)
                    begin
                        get_address = `LPM_TRUE;
                        get_data = `LPM_FALSE;
                        buffer = "";
                        character_count = 0;

                        if (start_address != end_address)
                        begin
                            for (address = start_address; address <= end_address; address = address+1)
                            begin
                                $fdisplay(ofp,"@%0h", address);

                                for (i = memory_width -1; i >= 0; i = i-1 )
                                begin
                                    hex[(i % 4)] =  memory_data1[i];

                                    if ((i % 4) == 0)
                                    begin
                                        $fwrite(ofp, "%0h", hex);
                                        hex = 0;
                                    end
                                end

                                $fwrite(ofp, "\n");
                            end
                            start_address = 0;
                            end_address = 0;
                            address = 0;
                            hex = 0;
                            memory_data1 = {(`LPM_MAX_WIDTH+1) {1'b0}};
                        end
                        else
                        begin
                            if (display_address == `LPM_TRUE)
                            begin
                                $fdisplay(ofp,"@%0h", address);
                                display_address = `LPM_FALSE;
                            end

                            for (i = memory_width -1; i >= 0; i = i-1 )
                            begin
                                hex[(i % 4)] =  memory_data1[i];

                                if ((i % 4) == 0)
                                begin
                                    $fwrite(ofp, "%0h", hex);
                                    hex = 0;
                                end
                            end

                            $fwrite(ofp, "\n");
                            address = 0;
                            hex = 0;
                            memory_data1 = {(`LPM_MAX_WIDTH+1) {1'b0}};
                        end
                    end
                    else
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid assigment.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                end
                else if ((get_width == `LPM_TRUE) || (get_depth == `LPM_TRUE))
                begin
                    if ((r >= "0") && (r <= "9"))
                        value = (value * 10) + (r - 'h30);
                    else
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid assignment to width/depth.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (get_address == `LPM_TRUE)
                begin
                    if (address_radix == "hex")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            value = 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            value = 10 + (r - 'h61);
                        else
                        begin
                            invalid_address = `LPM_TRUE;
                        end

                        address = (address * 16) + value;
                    end
                    else if ((address_radix == "dec"))
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `LPM_TRUE;
                        end

                        address = (address * 10) + value;
                    end
                    else if (address_radix == "uns")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `LPM_TRUE;
                        end

                        address = (address * 10) + value;
                    end
                    else if (address_radix == "bin")
                    begin
                        if ((r >= "0") && (r <= "1"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `LPM_TRUE;
                        end

                        address = (address * 2) + value;
                    end
                    else if (address_radix == "oct")
                    begin
                        if ((r >= "0") && (r <= "7"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `LPM_TRUE;
                        end

                        address = (address * 8) + value;
                    end

                    if ((r >= 65) && (r <= 90))
                        c = tolower(r);
                    else
                        c = r;

                    {tmp_char,buffer} = {buffer, c};
                end
                else if (get_data == `LPM_TRUE)
                begin
                    character_count = character_count +1;

                    if (data_radix == "hex")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            value = 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            value = 10 + (r - 'h61);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end

                        memory_data1 = (memory_data1 * 16) + value;
                    end
                    else if ((data_radix == "dec"))
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end

                        memory_data1 = (memory_data1 * 10) + value;
                    end
                    else if (data_radix == "uns")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end

                        memory_data1 = (memory_data1 * 10) + value;
                    end
                    else if (data_radix == "bin")
                    begin
                        if ((r >= "0") && (r <= "1"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end

                        memory_data1 = (memory_data1 * 2) + value;
                    end
                    else if (data_radix == "oct")
                    begin
                        if ((r >= "0") && (r <= "7"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end

                        memory_data1 = (memory_data1 * 8) + value;
                    end
                end
                else
                begin
                    first_rec = `LPM_TRUE;

                    if ((r >= 65) && (r <= 90))
                        c = tolower(r);
                    else
                        c = r;

                    {tmp_char,buffer} = {buffer, c};
                end
            end
            $fclose(ifp);
            $fclose(ofp);
        end
end
endtask // convert_mif2ver

/****************************************************************/
/* Read in Intel-hex format data to verilog format data.        */
/*  Intel-hex format    :nnaaaaattddddcc                        */
/****************************************************************/
task convert_hex2ver;
    input[`LPM_MAX_NAME_SZ*8 : 1] in_file;
    input width;
    output [`LPM_MAX_NAME_SZ*8 : 1] out_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] in_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] out_file;
    reg [8:1] c;
    reg [3:0] hex, tmp_char;
    reg done;
    reg error_status;
    reg first_rec;
    reg last_rec;

    integer width;
    integer ifp, ofp, r, r2;
    integer i, j, k, m, n;

    integer off_addr, nn, aaaa, tt, cc, aah, aal, dd, sum ;
    integer line_no;

begin
        done = `LPM_FALSE;
        error_status = `LPM_FALSE;
        first_rec = `LPM_FALSE;
        last_rec = `LPM_FALSE;

        off_addr= 0;
        nn= 0;
        aaaa= 0;
        tt= 0;
        cc= 0;
        aah= 0;
        aal= 0;
        dd= 0;
        sum = 0;
        line_no = 1;
        c = 0;
        hex = 0;

        if((in_file[4*8 : 1] == ".dat") || (in_file[4*8 : 1] == ".DAT"))
            out_file = in_file;
        else
        begin
            ifp = $fopen(in_file, "r");
            if (ifp == `LPM_NULL)
            begin
                $display("ERROR: cannot read %0s.", in_file);
                $display("Time: %0t  Instance: %m", $time);
                done = `LPM_TRUE;
            end

            out_file = in_file;

            if((out_file[4*8 : 1] == ".hex") || (out_file[4*8 : 1] == ".HEX"))
                out_file[3*8 : 1] = `LPM_EXT_STR;
            else
            begin
                $display("ERROR: Invalid input file name %0s. Expecting file with .hex extension and Intel-hex data format.", in_file);
                $display("Time: %0t  Instance: %m", $time);
                done = `LPM_TRUE;
            end

            if (!done)
            begin
                ofp = $fopen(out_file, "w");
                if (ofp == `LPM_NULL)
                begin
                    $display("ERROR : cannot write %0s.", out_file);
                    $display("Time: %0t  Instance: %m", $time);
                    done = `LPM_TRUE;
                end
            end

            while((!done) && (!error_status))
            begin : READER

                r = $fgetc(ifp);

                if (r == `LPM_EOF)
                begin
                    if(!first_rec)
                    begin
                        error_status = `LPM_TRUE;
                        $display("WARNING: %0s, Intel-hex data file is empty.", in_file);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else if(!last_rec)
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Missing the last record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (r == `LPM_COLON)
                begin
                    first_rec = `LPM_TRUE;
                    nn= 0;
                    aaaa= 0;
                    tt= 0;
                    cc= 0;
                    aah= 0;
                    aal= 0;
                    dd= 0;
                    sum = 0;

                    // get record length bytes
                    for (i = 0; i < 2; i = i+1)
                    begin
                        r = $fgetc(ifp);

                        if ((r >= "0") && (r <= "9"))
                            nn = (nn * 16) + (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            nn = (nn * 16) + 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            nn = (nn * 16) + 10 + (r - 'h61);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end
                    end

                    // get address bytes
                    for (i = 0; i < 4; i = i+1)
                    begin
                        r = $fgetc(ifp);

                        if ((r >= "0") && (r <= "9"))
                            hex = (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            hex = 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            hex = 10 + (r - 'h61);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end

                        aaaa = (aaaa * 16) + hex;

                        if (i < 2)
                            aal = (aal * 16) + hex;
                        else
                            aah = (aah * 16) + hex;
                    end

                    // get record type bytes
                    for (i = 0; i < 2; i = i+1)
                    begin
                        r = $fgetc(ifp);

                        if ((r >= "0") && (r <= "9"))
                            tt = (tt * 16) + (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            tt = (tt * 16) + 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            tt = (tt * 16) + 10 + (r - 'h61);
                        else
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                            done = `LPM_TRUE;
                            disable READER;
                        end
                    end

                    if((tt == 2) && (nn != 2) )
                    begin
                        error_status = `LPM_TRUE;
                        $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                        $display("Time: %0t  Instance: %m", $time);
                    end
                    else
                    begin

                        // get the sum of all the bytes for record length, address and record types
                        sum = nn + aah + aal + tt ;

                        // check the record type
                        case(tt)
                            // normal_record
                            8'h00 :
                            begin
                                first_rec = `LPM_TRUE;
                                i = 0;
                                k = width / `LPM_AWORD;
                                if ((width % `LPM_AWORD) != 0)
                                    k = k + 1;

                                // k = no. of bytes per entry.
                                while (i < nn)
                                begin
                                    $fdisplay(ofp,"@%0h", (aaaa + off_addr));
                                    for (j = 1; j <= k; j = j +1)
                                    begin
                                        if ((k - j +1) > nn)
                                        begin
                                            for(m = 1; m <= 2; m= m+1)
                                            begin
                                                if((((k-j)*8) + ((3-m)*4) - width) < 4)
                                                    $fwrite(ofp, "0");
                                            end
                                        end
                                        else
                                        begin
                                            // get the data bytes
                                            for(m = 1; m <= 2; m= m+1)
                                            begin
                                                r = $fgetc(ifp);

                                                if ((r >= "0") && (r <= "9"))
                                                    hex = (r - 'h30);
                                                else if ((r >= "A") && (r <= "F"))
                                                    hex = 10 + (r - 'h41);
                                                else if ((r >= "a") && (r <= "f"))
                                                    hex = 10 + (r - 'h61);
                                                else
                                                begin
                                                    error_status = `LPM_TRUE;
                                                    $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                                    $display("Time: %0t  Instance: %m", $time);
                                                    done = `LPM_TRUE;
                                                    disable READER;
                                                end

                                                if((((k-j)*8) + ((3-m)*4) - width) < 4)
                                                    $fwrite(ofp, "%h", hex);
                                                dd = (dd * 16) + hex;

                                                if(m % 2 == 0)
                                                begin
                                                    sum = sum + dd;
                                                    dd = 0;
                                                end
                                            end
                                        end
                                    end
                                    $fwrite(ofp, "\n");

                                    i = i + k;
                                    aaaa = aaaa + 1;
                                end // end of while (i < nn)
                            end
                            // last record
                            8'h01:
                            begin
                                last_rec = `LPM_TRUE;
                                done = `LPM_TRUE;
                            end
                            // address base record
                            8'h02:
                            begin
                                off_addr= 0;

                                // get the extended segment address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `LPM_TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        $display("Time: %0t  Instance: %m", $time);
                                        done = `LPM_TRUE;
                                        disable READER;
                                    end

                                    off_addr = (off_addr * `LPM_H10) + hex;
                                    dd = (dd * 16) + hex;

                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end

                                off_addr = off_addr * `LPM_H10;
                            end
                            // address base record
                            8'h03:
                                // get the start segment address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `LPM_TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        $display("Time: %0t  Instance: %m", $time);
                                        done = `LPM_TRUE;
                                        disable READER;
                                    end
                                    dd = (dd * 16) + hex;

                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end
                            // address base record
                            8'h04:
                            begin
                                off_addr= 0;

                                // get the extended linear address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `LPM_TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        $display("Time: %0t  Instance: %m", $time);
                                        done = `LPM_TRUE;
                                        disable READER;
                                    end

                                    off_addr = (off_addr * `LPM_H10) + hex;
                                    dd = (dd * 16) + hex;

                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end

                                off_addr = off_addr * `LPM_H10000;
                            end
                            // address base record
                            8'h05:
                                // get the start linear address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `LPM_TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        $display("Time: %0t  Instance: %m", $time);
                                        done = `LPM_TRUE;
                                        disable READER;
                                    end
                                    dd = (dd * 16) + hex;

                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end
                            default:
                            begin
                                error_status = `LPM_TRUE;
                                $display("ERROR: %0s, line %0d, Unknown record type.", in_file, line_no);
                                $display("Time: %0t  Instance: %m", $time);
                            end
                        endcase

                        // get the checksum bytes
                        for (i = 0; i < 2; i = i+1)
                        begin
                            r = $fgetc(ifp);

                            if ((r >= "0") && (r <= "9"))
                                cc = (cc * 16) + (r - 'h30);
                            else if ((r >= "A") && (r <= "F"))
                                cc = 10 + (cc * 16) + (r - 'h41);
                            else if ((r >= "a") && (r <= "f"))
                                cc = 10 + (cc * 16) + (r - 'h61);
                            else
                            begin
                                error_status = `LPM_TRUE;
                                $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                $display("Time: %0t  Instance: %m", $time);
                                done = `LPM_TRUE;
                                disable READER;
                            end
                        end

                        // Perform check sum.
                        if(((~sum+1)& `LPM_MASK15) != cc)
                        begin
                            error_status = `LPM_TRUE;
                            $display("ERROR: %0s, line %0d, Invalid checksum.", in_file, line_no);
                            $display("Time: %0t  Instance: %m", $time);
                        end
                    end
                end
                else if ((r == `LPM_NEWLINE) || (r == `LPM_CARRIAGE_RETURN))
                begin
                    line_no = line_no +1;
                end
                else if (r == `LPM_SPACE)
                begin
                    // continue to next character;
                end
                else
                begin
                    error_status = `LPM_TRUE;
                    $display("ERROR:%0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                    $display("Time: %0t  Instance: %m", $time);
                    done = `LPM_TRUE;
                end
            end
            $fclose(ifp);
            $fclose(ofp);
        end
end
endtask // convert_hex2ver

task convert_to_ver_file;
    input[`LPM_MAX_NAME_SZ*8 : 1] in_file;
    input width;
    output [`LPM_MAX_NAME_SZ*8 : 1] out_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] in_file;
    reg [`LPM_MAX_NAME_SZ*8 : 1] out_file;
    integer width;
begin

        if((in_file[4*8 : 1] == ".hex") || (in_file[4*8 : 1] == ".HEX") ||
            (in_file[4*8 : 1] == ".dat") || (in_file[4*8 : 1] == ".DAT"))
            convert_hex2ver(in_file, width, out_file);
        else if((in_file[4*8 : 1] == ".mif") || (in_file[4*8 : 1] == ".MIF"))
            convert_mif2ver(in_file, width, out_file);
        else
        begin
            $display("ERROR: Invalid input file name %0s. Expecting file with .hex extension (with Intel-hex data format) or .mif extension (with Altera-mif data format).", in_file);
            $display("Time: %0t  Instance: %m", $time);
        end
end
endtask // convert_to_ver_file

endmodule // LPM_MEMORY_INITIALIZATION


//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  LPM_HINT_EVALUATION
//
// Description     :  Common function to grep the value of altera specific parameters
//                    within the lpm_hint parameter.
//
// Limitation      :  No error checking to check whether the content of the lpm_hint
//                    is valid or not.
//
// Results expected:  If the target parameter found, return the value of the parameter.
//                    Otherwise, return empty string.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module LPM_HINT_EVALUATION;

// FUNCTON DECLARATION

// This function will search through the string (given string) to look for a match for the
// a given parameter(compare_param_name). It will return the value for the given parameter.
function [8*200:1] GET_PARAMETER_VALUE;
    input [8*200:1] given_string;  // string to be searched
    input [8*50:1] compare_param_name; // parameter name to be looking for in the given_string.
    integer param_value_char_count; // to indicate current character count in the param_value
    integer param_name_char_count;  // to indicate current character count in the param_name
    integer white_space_count;

    reg extract_param_value; // if 1 mean extracting parameters value from given string
    reg extract_param_name;  // if 1 mean extracting parameters name from given string
    reg param_found; // to indicate whether compare_param_name have been found in the given_string
    reg include_white_space; // if 1, include white space in the parameter value

    reg [8*200:1] reg_string; // to store the value of the given string
    reg [8*50:1] param_name;  // to store parameter name
    reg [8*20:1] param_value; // to store parameter value
    reg [8:1] tmp; // to get the value of the current byte
begin
    reg_string = given_string;
    param_value_char_count = 0;
    param_name_char_count =0;
    extract_param_value = 1;
    extract_param_name = 0;
    param_found = 0;
    include_white_space = 0;
    white_space_count = 0;

    tmp = reg_string[8:1];

    // checking every bytes of the reg_string from right to left.
    while ((tmp != 0 ) && (param_found != 1))
    begin
        tmp = reg_string[8:1];

        //if tmp != ' ' or should include white space (trailing white space are ignored)
        if((tmp != 32) || (include_white_space == 1))
        begin
            if(tmp == 32)
            begin
                white_space_count = 1;
            end
            else if(tmp == 61)  // if tmp = '='
            begin
                extract_param_value = 0;
                extract_param_name =  1;  // subsequent bytes should be part of param_name
                include_white_space = 0;  // ignore the white space (if any) between param_name and '='
                white_space_count = 0;
                param_value = param_value >> (8 * (20 - param_value_char_count));
                param_value_char_count = 0;
            end
            else if (tmp == 44) // if tmp = ','
            begin
                extract_param_value = 1; // subsequent bytes should be part of param_value
                extract_param_name =  0;
                param_name = param_name >> (8 * (50 - param_name_char_count));
                param_name_char_count = 0;
                if(param_name == compare_param_name)
                    param_found = 1;  // the compare_param_name have been found in the reg_string
            end
            else
            begin
                if(extract_param_value == 1)
                begin
                    param_value_char_count = param_value_char_count + white_space_count + 1;
                    include_white_space = 1;
                    if(white_space_count > 0)
                    begin
                        param_value = {8'b100000, param_value[20*8:9]};
                        white_space_count = 0;
                    end
                    param_value = {tmp, param_value[20*8:9]};
                end
                else if(extract_param_name == 1)
                begin
                    param_name = {tmp, param_name[50*8:9]};
                    param_name_char_count = param_name_char_count + 1;
                end
            end
        end
        reg_string = reg_string >> 8;  // shift 1 byte to the right
    end

    // for the case whether param_name is the left most part of the reg_string
    if(extract_param_name == 1)
    begin
        param_name = param_name >> (8 * (50 - param_name_char_count));

        if(param_name == compare_param_name)
            param_found = 1;
    end

    if (param_found == 1)
        GET_PARAMETER_VALUE = param_value;   // return the value of the parameter been looking for
    else
        GET_PARAMETER_VALUE = "";  // return empty string if parameter not found

end
endfunction

endmodule // LPM_HINT_EVALUATION

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module LPM_DEVICE_FAMILIES;

function IS_FAMILY_CYCLONE;
    input[8*20:1] device;
    reg is_cyclone;
begin
    if ((device == "Cyclone") || (device == "CYCLONE") || (device == "cyclone") || (device == "ACEX2K") || (device == "acex2k") || (device == "ACEX 2K") || (device == "acex 2k") || (device == "Tornado") || (device == "TORNADO") || (device == "tornado"))
        is_cyclone = 1;
    else
        is_cyclone = 0;

    IS_FAMILY_CYCLONE  = is_cyclone;
end
endfunction //IS_FAMILY_CYCLONE

function IS_FAMILY_MAX3000A;
    input[8*20:1] device;
    reg is_max3000a;
begin
    if ((device == "MAX3000A") || (device == "max3000a") || (device == "MAX 3000A") || (device == "max 3000a"))
        is_max3000a = 1;
    else
        is_max3000a = 0;

    IS_FAMILY_MAX3000A  = is_max3000a;
end
endfunction //IS_FAMILY_MAX3000A

function IS_FAMILY_MAX7000A;
    input[8*20:1] device;
    reg is_max7000a;
begin
    if ((device == "MAX7000A") || (device == "max7000a") || (device == "MAX 7000A") || (device == "max 7000a"))
        is_max7000a = 1;
    else
        is_max7000a = 0;

    IS_FAMILY_MAX7000A  = is_max7000a;
end
endfunction //IS_FAMILY_MAX7000A

function IS_FAMILY_MAX7000AE;
    input[8*20:1] device;
    reg is_max7000ae;
begin
    if ((device == "MAX7000AE") || (device == "max7000ae") || (device == "MAX 7000AE") || (device == "max 7000ae"))
        is_max7000ae = 1;
    else
        is_max7000ae = 0;

    IS_FAMILY_MAX7000AE  = is_max7000ae;
end
endfunction //IS_FAMILY_MAX7000AE

function IS_FAMILY_MAX7000B;
    input[8*20:1] device;
    reg is_max7000b;
begin
    if ((device == "MAX7000B") || (device == "max7000b") || (device == "MAX 7000B") || (device == "max 7000b"))
        is_max7000b = 1;
    else
        is_max7000b = 0;

    IS_FAMILY_MAX7000B  = is_max7000b;
end
endfunction //IS_FAMILY_MAX7000B

function IS_FAMILY_MAX7000S;
    input[8*20:1] device;
    reg is_max7000s;
begin
    if ((device == "MAX7000S") || (device == "max7000s") || (device == "MAX 7000S") || (device == "max 7000s"))
        is_max7000s = 1;
    else
        is_max7000s = 0;

    IS_FAMILY_MAX7000S  = is_max7000s;
end
endfunction //IS_FAMILY_MAX7000S

function IS_FAMILY_STRATIXGX;
    input[8*20:1] device;
    reg is_stratixgx;
begin
    if ((device == "Stratix GX") || (device == "STRATIX GX") || (device == "stratix gx") || (device == "Stratix-GX") || (device == "STRATIX-GX") || (device == "stratix-gx") || (device == "StratixGX") || (device == "STRATIXGX") || (device == "stratixgx") || (device == "Aurora") || (device == "AURORA") || (device == "aurora"))
        is_stratixgx = 1;
    else
        is_stratixgx = 0;

    IS_FAMILY_STRATIXGX  = is_stratixgx;
end
endfunction //IS_FAMILY_STRATIXGX

function IS_FAMILY_STRATIX;
    input[8*20:1] device;
    reg is_stratix;
begin
    if ((device == "Stratix") || (device == "STRATIX") || (device == "stratix") || (device == "Yeager") || (device == "YEAGER") || (device == "yeager"))
        is_stratix = 1;
    else
        is_stratix = 0;

    IS_FAMILY_STRATIX  = is_stratix;
end
endfunction //IS_FAMILY_STRATIX

function FEATURE_FAMILY_BASE_STRATIX;
    input[8*20:1] device;
    reg var_family_base_stratix;
begin
    if (IS_FAMILY_STRATIX(device) || IS_FAMILY_STRATIXGX(device) )
        var_family_base_stratix = 1;
    else
        var_family_base_stratix = 0;

    FEATURE_FAMILY_BASE_STRATIX  = var_family_base_stratix;
end
endfunction //FEATURE_FAMILY_BASE_STRATIX

function FEATURE_FAMILY_BASE_CYCLONE;
    input[8*20:1] device;
    reg var_family_base_cyclone;
begin
    if (IS_FAMILY_CYCLONE(device) )
        var_family_base_cyclone = 1;
    else
        var_family_base_cyclone = 0;

    FEATURE_FAMILY_BASE_CYCLONE  = var_family_base_cyclone;
end
endfunction //FEATURE_FAMILY_BASE_CYCLONE

function FEATURE_FAMILY_MAX;
    input[8*20:1] device;
    reg var_family_max;
begin
    if ((device == "MAX5000") || IS_FAMILY_MAX3000A(device) || (device == "MAX7000") || IS_FAMILY_MAX7000A(device) || IS_FAMILY_MAX7000AE(device) || (device == "MAX7000E") || IS_FAMILY_MAX7000S(device) || IS_FAMILY_MAX7000B(device) || (device == "MAX9000") )
        var_family_max = 1;
    else
        var_family_max = 0;

    FEATURE_FAMILY_MAX  = var_family_max;
end
endfunction //FEATURE_FAMILY_MAX

function IS_VALID_FAMILY;
    input[8*20:1] device;
    reg is_valid;
begin
    if (((device == "Arria 10") || (device == "ARRIA 10") || (device == "arria 10") || (device == "Arria10") || (device == "ARRIA10") || (device == "arria10") || (device == "Arria VI") || (device == "ARRIA VI") || (device == "arria vi") || (device == "ArriaVI") || (device == "ARRIAVI") || (device == "arriavi") || (device == "Night Fury") || (device == "NIGHT FURY") || (device == "night fury") || (device == "nightfury") || (device == "NIGHTFURY") || (device == "Arria 10 (GX/SX/GT)") || (device == "ARRIA 10 (GX/SX/GT)") || (device == "arria 10 (gx/sx/gt)") || (device == "Arria10(GX/SX/GT)") || (device == "ARRIA10(GX/SX/GT)") || (device == "arria10(gx/sx/gt)") || (device == "Arria 10 (GX)") || (device == "ARRIA 10 (GX)") || (device == "arria 10 (gx)") || (device == "Arria10(GX)") || (device == "ARRIA10(GX)") || (device == "arria10(gx)") || (device == "Arria 10 (SX)") || (device == "ARRIA 10 (SX)") || (device == "arria 10 (sx)") || (device == "Arria10(SX)") || (device == "ARRIA10(SX)") || (device == "arria10(sx)") || (device == "Arria 10 (GT)") || (device == "ARRIA 10 (GT)") || (device == "arria 10 (gt)") || (device == "Arria10(GT)") || (device == "ARRIA10(GT)") || (device == "arria10(gt)"))
    || ((device == "Arria GX") || (device == "ARRIA GX") || (device == "arria gx") || (device == "ArriaGX") || (device == "ARRIAGX") || (device == "arriagx") || (device == "Stratix II GX Lite") || (device == "STRATIX II GX LITE") || (device == "stratix ii gx lite") || (device == "StratixIIGXLite") || (device == "STRATIXIIGXLITE") || (device == "stratixiigxlite"))
    || ((device == "Arria II GX") || (device == "ARRIA II GX") || (device == "arria ii gx") || (device == "ArriaIIGX") || (device == "ARRIAIIGX") || (device == "arriaiigx") || (device == "Arria IIGX") || (device == "ARRIA IIGX") || (device == "arria iigx") || (device == "ArriaII GX") || (device == "ARRIAII GX") || (device == "arriaii gx") || (device == "Arria II") || (device == "ARRIA II") || (device == "arria ii") || (device == "ArriaII") || (device == "ARRIAII") || (device == "arriaii") || (device == "Arria II (GX/E)") || (device == "ARRIA II (GX/E)") || (device == "arria ii (gx/e)") || (device == "ArriaII(GX/E)") || (device == "ARRIAII(GX/E)") || (device == "arriaii(gx/e)") || (device == "PIRANHA") || (device == "piranha"))
    || ((device == "Arria II GZ") || (device == "ARRIA II GZ") || (device == "arria ii gz") || (device == "ArriaII GZ") || (device == "ARRIAII GZ") || (device == "arriaii gz") || (device == "Arria IIGZ") || (device == "ARRIA IIGZ") || (device == "arria iigz") || (device == "ArriaIIGZ") || (device == "ARRIAIIGZ") || (device == "arriaiigz"))
    || ((device == "Arria V GZ") || (device == "ARRIA V GZ") || (device == "arria v gz") || (device == "ArriaVGZ") || (device == "ARRIAVGZ") || (device == "arriavgz"))
    || ((device == "Arria V") || (device == "ARRIA V") || (device == "arria v") || (device == "Arria V (GT/GX)") || (device == "ARRIA V (GT/GX)") || (device == "arria v (gt/gx)") || (device == "ArriaV(GT/GX)") || (device == "ARRIAV(GT/GX)") || (device == "arriav(gt/gx)") || (device == "ArriaV") || (device == "ARRIAV") || (device == "arriav") || (device == "Arria V (GT/GX/ST/SX)") || (device == "ARRIA V (GT/GX/ST/SX)") || (device == "arria v (gt/gx/st/sx)") || (device == "ArriaV(GT/GX/ST/SX)") || (device == "ARRIAV(GT/GX/ST/SX)") || (device == "arriav(gt/gx/st/sx)") || (device == "Arria V (GT)") || (device == "ARRIA V (GT)") || (device == "arria v (gt)") || (device == "ArriaV(GT)") || (device == "ARRIAV(GT)") || (device == "arriav(gt)") || (device == "Arria V (GX)") || (device == "ARRIA V (GX)") || (device == "arria v (gx)") || (device == "ArriaV(GX)") || (device == "ARRIAV(GX)") || (device == "arriav(gx)") || (device == "Arria V (ST)") || (device == "ARRIA V (ST)") || (device == "arria v (st)") || (device == "ArriaV(ST)") || (device == "ARRIAV(ST)") || (device == "arriav(st)") || (device == "Arria V (SX)") || (device == "ARRIA V (SX)") || (device == "arria v (sx)") || (device == "ArriaV(SX)") || (device == "ARRIAV(SX)") || (device == "arriav(sx)"))
    || ((device == "BS") || (device == "bs"))
    || ((device == "Cyclone II") || (device == "CYCLONE II") || (device == "cyclone ii") || (device == "Cycloneii") || (device == "CYCLONEII") || (device == "cycloneii") || (device == "Magellan") || (device == "MAGELLAN") || (device == "magellan") || (device == "CycloneII") || (device == "CYCLONEII") || (device == "cycloneii"))
    || ((device == "Cyclone III LS") || (device == "CYCLONE III LS") || (device == "cyclone iii ls") || (device == "CycloneIIILS") || (device == "CYCLONEIIILS") || (device == "cycloneiiils") || (device == "Cyclone III LPS") || (device == "CYCLONE III LPS") || (device == "cyclone iii lps") || (device == "Cyclone LPS") || (device == "CYCLONE LPS") || (device == "cyclone lps") || (device == "CycloneLPS") || (device == "CYCLONELPS") || (device == "cyclonelps") || (device == "Tarpon") || (device == "TARPON") || (device == "tarpon") || (device == "Cyclone IIIE") || (device == "CYCLONE IIIE") || (device == "cyclone iiie"))
    || ((device == "Cyclone III") || (device == "CYCLONE III") || (device == "cyclone iii") || (device == "CycloneIII") || (device == "CYCLONEIII") || (device == "cycloneiii") || (device == "Barracuda") || (device == "BARRACUDA") || (device == "barracuda") || (device == "Cuda") || (device == "CUDA") || (device == "cuda") || (device == "CIII") || (device == "ciii"))
    || ((device == "Cyclone IV E") || (device == "CYCLONE IV E") || (device == "cyclone iv e") || (device == "CycloneIV E") || (device == "CYCLONEIV E") || (device == "cycloneiv e") || (device == "Cyclone IVE") || (device == "CYCLONE IVE") || (device == "cyclone ive") || (device == "CycloneIVE") || (device == "CYCLONEIVE") || (device == "cycloneive"))
    || ((device == "Cyclone IV GX") || (device == "CYCLONE IV GX") || (device == "cyclone iv gx") || (device == "Cyclone IVGX") || (device == "CYCLONE IVGX") || (device == "cyclone ivgx") || (device == "CycloneIV GX") || (device == "CYCLONEIV GX") || (device == "cycloneiv gx") || (device == "CycloneIVGX") || (device == "CYCLONEIVGX") || (device == "cycloneivgx") || (device == "Cyclone IV") || (device == "CYCLONE IV") || (device == "cyclone iv") || (device == "CycloneIV") || (device == "CYCLONEIV") || (device == "cycloneiv") || (device == "Cyclone IV (GX)") || (device == "CYCLONE IV (GX)") || (device == "cyclone iv (gx)") || (device == "CycloneIV(GX)") || (device == "CYCLONEIV(GX)") || (device == "cycloneiv(gx)") || (device == "Cyclone III GX") || (device == "CYCLONE III GX") || (device == "cyclone iii gx") || (device == "CycloneIII GX") || (device == "CYCLONEIII GX") || (device == "cycloneiii gx") || (device == "Cyclone IIIGX") || (device == "CYCLONE IIIGX") || (device == "cyclone iiigx") || (device == "CycloneIIIGX") || (device == "CYCLONEIIIGX") || (device == "cycloneiiigx") || (device == "Cyclone III GL") || (device == "CYCLONE III GL") || (device == "cyclone iii gl") || (device == "CycloneIII GL") || (device == "CYCLONEIII GL") || (device == "cycloneiii gl") || (device == "Cyclone IIIGL") || (device == "CYCLONE IIIGL") || (device == "cyclone iiigl") || (device == "CycloneIIIGL") || (device == "CYCLONEIIIGL") || (device == "cycloneiiigl") || (device == "Stingray") || (device == "STINGRAY") || (device == "stingray"))
    || ((device == "Cyclone V") || (device == "CYCLONE V") || (device == "cyclone v") || (device == "CycloneV") || (device == "CYCLONEV") || (device == "cyclonev") || (device == "Cyclone V (GT/GX/E/SX)") || (device == "CYCLONE V (GT/GX/E/SX)") || (device == "cyclone v (gt/gx/e/sx)") || (device == "CycloneV(GT/GX/E/SX)") || (device == "CYCLONEV(GT/GX/E/SX)") || (device == "cyclonev(gt/gx/e/sx)") || (device == "Cyclone V (E/GX/GT/SX/SE/ST)") || (device == "CYCLONE V (E/GX/GT/SX/SE/ST)") || (device == "cyclone v (e/gx/gt/sx/se/st)") || (device == "CycloneV(E/GX/GT/SX/SE/ST)") || (device == "CYCLONEV(E/GX/GT/SX/SE/ST)") || (device == "cyclonev(e/gx/gt/sx/se/st)") || (device == "Cyclone V (E)") || (device == "CYCLONE V (E)") || (device == "cyclone v (e)") || (device == "CycloneV(E)") || (device == "CYCLONEV(E)") || (device == "cyclonev(e)") || (device == "Cyclone V (GX)") || (device == "CYCLONE V (GX)") || (device == "cyclone v (gx)") || (device == "CycloneV(GX)") || (device == "CYCLONEV(GX)") || (device == "cyclonev(gx)") || (device == "Cyclone V (GT)") || (device == "CYCLONE V (GT)") || (device == "cyclone v (gt)") || (device == "CycloneV(GT)") || (device == "CYCLONEV(GT)") || (device == "cyclonev(gt)") || (device == "Cyclone V (SX)") || (device == "CYCLONE V (SX)") || (device == "cyclone v (sx)") || (device == "CycloneV(SX)") || (device == "CYCLONEV(SX)") || (device == "cyclonev(sx)") || (device == "Cyclone V (SE)") || (device == "CYCLONE V (SE)") || (device == "cyclone v (se)") || (device == "CycloneV(SE)") || (device == "CYCLONEV(SE)") || (device == "cyclonev(se)") || (device == "Cyclone V (ST)") || (device == "CYCLONE V (ST)") || (device == "cyclone v (st)") || (device == "CycloneV(ST)") || (device == "CYCLONEV(ST)") || (device == "cyclonev(st)"))
    || ((device == "Cyclone") || (device == "CYCLONE") || (device == "cyclone") || (device == "ACEX2K") || (device == "acex2k") || (device == "ACEX 2K") || (device == "acex 2k") || (device == "Tornado") || (device == "TORNADO") || (device == "tornado"))
    || ((device == "HardCopy II") || (device == "HARDCOPY II") || (device == "hardcopy ii") || (device == "HardCopyII") || (device == "HARDCOPYII") || (device == "hardcopyii") || (device == "Fusion") || (device == "FUSION") || (device == "fusion"))
    || ((device == "HardCopy III") || (device == "HARDCOPY III") || (device == "hardcopy iii") || (device == "HardCopyIII") || (device == "HARDCOPYIII") || (device == "hardcopyiii") || (device == "HCX") || (device == "hcx"))
    || ((device == "HardCopy IV") || (device == "HARDCOPY IV") || (device == "hardcopy iv") || (device == "HardCopyIV") || (device == "HARDCOPYIV") || (device == "hardcopyiv") || (device == "HardCopy IV (GX)") || (device == "HARDCOPY IV (GX)") || (device == "hardcopy iv (gx)") || (device == "HardCopy IV (E)") || (device == "HARDCOPY IV (E)") || (device == "hardcopy iv (e)") || (device == "HardCopyIV(GX)") || (device == "HARDCOPYIV(GX)") || (device == "hardcopyiv(gx)") || (device == "HardCopyIV(E)") || (device == "HARDCOPYIV(E)") || (device == "hardcopyiv(e)") || (device == "HCXIV") || (device == "hcxiv") || (device == "HardCopy IV (GX/E)") || (device == "HARDCOPY IV (GX/E)") || (device == "hardcopy iv (gx/e)") || (device == "HardCopy IV (E/GX)") || (device == "HARDCOPY IV (E/GX)") || (device == "hardcopy iv (e/gx)") || (device == "HardCopyIV(GX/E)") || (device == "HARDCOPYIV(GX/E)") || (device == "hardcopyiv(gx/e)") || (device == "HardCopyIV(E/GX)") || (device == "HARDCOPYIV(E/GX)") || (device == "hardcopyiv(e/gx)"))
    || ((device == "MAX 10") || (device == "max 10") || (device == "MAX 10 FPGA") || (device == "max 10 fpga") || (device == "Zippleback") || (device == "ZIPPLEBACK") || (device == "zippleback") || (device == "MAX10") || (device == "max10") || (device == "MAX 10 (DA/DF/DC/SA/SC)") || (device == "max 10 (da/df/dc/sa/sc)") || (device == "MAX10(DA/DF/DC/SA/SC)") || (device == "max10(da/df/dc/sa/sc)") || (device == "MAX 10 (DA)") || (device == "max 10 (da)") || (device == "MAX10(DA)") || (device == "max10(da)") || (device == "MAX 10 (DF)") || (device == "max 10 (df)") || (device == "MAX10(DF)") || (device == "max10(df)") || (device == "MAX 10 (DC)") || (device == "max 10 (dc)") || (device == "MAX10(DC)") || (device == "max10(dc)") || (device == "MAX 10 (SA)") || (device == "max 10 (sa)") || (device == "MAX10(SA)") || (device == "max10(sa)") || (device == "MAX 10 (SC)") || (device == "max 10 (sc)") || (device == "MAX10(SC)") || (device == "max10(sc)"))
    || ((device == "MAX II") || (device == "max ii") || (device == "MAXII") || (device == "maxii") || (device == "Tsunami") || (device == "TSUNAMI") || (device == "tsunami"))
    || ((device == "MAX V") || (device == "max v") || (device == "MAXV") || (device == "maxv") || (device == "Jade") || (device == "JADE") || (device == "jade"))
    || ((device == "MAX3000A") || (device == "max3000a") || (device == "MAX 3000A") || (device == "max 3000a"))
    || ((device == "MAX7000A") || (device == "max7000a") || (device == "MAX 7000A") || (device == "max 7000a"))
    || ((device == "MAX7000AE") || (device == "max7000ae") || (device == "MAX 7000AE") || (device == "max 7000ae"))
    || ((device == "MAX7000B") || (device == "max7000b") || (device == "MAX 7000B") || (device == "max 7000b"))
    || ((device == "MAX7000S") || (device == "max7000s") || (device == "MAX 7000S") || (device == "max 7000s"))
    || ((device == "Stratix 10") || (device == "STRATIX 10") || (device == "stratix 10") || (device == "Stratix10") || (device == "STRATIX10") || (device == "stratix10") || (device == "nadder") || (device == "NADDER") || (device == "Stratix 10 (GX/SX)") || (device == "STRATIX 10 (GX/SX)") || (device == "stratix 10 (gx/sx)") || (device == "Stratix10(GX/SX)") || (device == "STRATIX10(GX/SX)") || (device == "stratix10(gx/sx)") || (device == "Stratix 10 (GX)") || (device == "STRATIX 10 (GX)") || (device == "stratix 10 (gx)") || (device == "Stratix10(GX)") || (device == "STRATIX10(GX)") || (device == "stratix10(gx)") || (device == "Stratix 10 (SX)") || (device == "STRATIX 10 (SX)") || (device == "stratix 10 (sx)") || (device == "Stratix10(SX)") || (device == "STRATIX10(SX)") || (device == "stratix10(sx)"))
    || ((device == "Stratix GX") || (device == "STRATIX GX") || (device == "stratix gx") || (device == "Stratix-GX") || (device == "STRATIX-GX") || (device == "stratix-gx") || (device == "StratixGX") || (device == "STRATIXGX") || (device == "stratixgx") || (device == "Aurora") || (device == "AURORA") || (device == "aurora"))
    || ((device == "Stratix II GX") || (device == "STRATIX II GX") || (device == "stratix ii gx") || (device == "StratixIIGX") || (device == "STRATIXIIGX") || (device == "stratixiigx"))
    || ((device == "Stratix II") || (device == "STRATIX II") || (device == "stratix ii") || (device == "StratixII") || (device == "STRATIXII") || (device == "stratixii") || (device == "Armstrong") || (device == "ARMSTRONG") || (device == "armstrong"))
    || ((device == "Stratix III") || (device == "STRATIX III") || (device == "stratix iii") || (device == "StratixIII") || (device == "STRATIXIII") || (device == "stratixiii") || (device == "Titan") || (device == "TITAN") || (device == "titan") || (device == "SIII") || (device == "siii"))
    || ((device == "Stratix IV") || (device == "STRATIX IV") || (device == "stratix iv") || (device == "TGX") || (device == "tgx") || (device == "StratixIV") || (device == "STRATIXIV") || (device == "stratixiv") || (device == "Stratix IV (GT)") || (device == "STRATIX IV (GT)") || (device == "stratix iv (gt)") || (device == "Stratix IV (GX)") || (device == "STRATIX IV (GX)") || (device == "stratix iv (gx)") || (device == "Stratix IV (E)") || (device == "STRATIX IV (E)") || (device == "stratix iv (e)") || (device == "StratixIV(GT)") || (device == "STRATIXIV(GT)") || (device == "stratixiv(gt)") || (device == "StratixIV(GX)") || (device == "STRATIXIV(GX)") || (device == "stratixiv(gx)") || (device == "StratixIV(E)") || (device == "STRATIXIV(E)") || (device == "stratixiv(e)") || (device == "StratixIIIGX") || (device == "STRATIXIIIGX") || (device == "stratixiiigx") || (device == "Stratix IV (GT/GX/E)") || (device == "STRATIX IV (GT/GX/E)") || (device == "stratix iv (gt/gx/e)") || (device == "Stratix IV (GT/E/GX)") || (device == "STRATIX IV (GT/E/GX)") || (device == "stratix iv (gt/e/gx)") || (device == "Stratix IV (E/GT/GX)") || (device == "STRATIX IV (E/GT/GX)") || (device == "stratix iv (e/gt/gx)") || (device == "Stratix IV (E/GX/GT)") || (device == "STRATIX IV (E/GX/GT)") || (device == "stratix iv (e/gx/gt)") || (device == "StratixIV(GT/GX/E)") || (device == "STRATIXIV(GT/GX/E)") || (device == "stratixiv(gt/gx/e)") || (device == "StratixIV(GT/E/GX)") || (device == "STRATIXIV(GT/E/GX)") || (device == "stratixiv(gt/e/gx)") || (device == "StratixIV(E/GX/GT)") || (device == "STRATIXIV(E/GX/GT)") || (device == "stratixiv(e/gx/gt)") || (device == "StratixIV(E/GT/GX)") || (device == "STRATIXIV(E/GT/GX)") || (device == "stratixiv(e/gt/gx)") || (device == "Stratix IV (GX/E)") || (device == "STRATIX IV (GX/E)") || (device == "stratix iv (gx/e)") || (device == "StratixIV(GX/E)") || (device == "STRATIXIV(GX/E)") || (device == "stratixiv(gx/e)"))
    || ((device == "Stratix V") || (device == "STRATIX V") || (device == "stratix v") || (device == "StratixV") || (device == "STRATIXV") || (device == "stratixv") || (device == "Stratix V (GS)") || (device == "STRATIX V (GS)") || (device == "stratix v (gs)") || (device == "StratixV(GS)") || (device == "STRATIXV(GS)") || (device == "stratixv(gs)") || (device == "Stratix V (GT)") || (device == "STRATIX V (GT)") || (device == "stratix v (gt)") || (device == "StratixV(GT)") || (device == "STRATIXV(GT)") || (device == "stratixv(gt)") || (device == "Stratix V (GX)") || (device == "STRATIX V (GX)") || (device == "stratix v (gx)") || (device == "StratixV(GX)") || (device == "STRATIXV(GX)") || (device == "stratixv(gx)") || (device == "Stratix V (GS/GX)") || (device == "STRATIX V (GS/GX)") || (device == "stratix v (gs/gx)") || (device == "StratixV(GS/GX)") || (device == "STRATIXV(GS/GX)") || (device == "stratixv(gs/gx)") || (device == "Stratix V (GS/GT)") || (device == "STRATIX V (GS/GT)") || (device == "stratix v (gs/gt)") || (device == "StratixV(GS/GT)") || (device == "STRATIXV(GS/GT)") || (device == "stratixv(gs/gt)") || (device == "Stratix V (GT/GX)") || (device == "STRATIX V (GT/GX)") || (device == "stratix v (gt/gx)") || (device == "StratixV(GT/GX)") || (device == "STRATIXV(GT/GX)") || (device == "stratixv(gt/gx)") || (device == "Stratix V (GX/GS)") || (device == "STRATIX V (GX/GS)") || (device == "stratix v (gx/gs)") || (device == "StratixV(GX/GS)") || (device == "STRATIXV(GX/GS)") || (device == "stratixv(gx/gs)") || (device == "Stratix V (GT/GS)") || (device == "STRATIX V (GT/GS)") || (device == "stratix v (gt/gs)") || (device == "StratixV(GT/GS)") || (device == "STRATIXV(GT/GS)") || (device == "stratixv(gt/gs)") || (device == "Stratix V (GX/GT)") || (device == "STRATIX V (GX/GT)") || (device == "stratix v (gx/gt)") || (device == "StratixV(GX/GT)") || (device == "STRATIXV(GX/GT)") || (device == "stratixv(gx/gt)") || (device == "Stratix V (GS/GT/GX)") || (device == "STRATIX V (GS/GT/GX)") || (device == "stratix v (gs/gt/gx)") || (device == "Stratix V (GS/GX/GT)") || (device == "STRATIX V (GS/GX/GT)") || (device == "stratix v (gs/gx/gt)") || (device == "Stratix V (GT/GS/GX)") || (device == "STRATIX V (GT/GS/GX)") || (device == "stratix v (gt/gs/gx)") || (device == "Stratix V (GT/GX/GS)") || (device == "STRATIX V (GT/GX/GS)") || (device == "stratix v (gt/gx/gs)") || (device == "Stratix V (GX/GS/GT)") || (device == "STRATIX V (GX/GS/GT)") || (device == "stratix v (gx/gs/gt)") || (device == "Stratix V (GX/GT/GS)") || (device == "STRATIX V (GX/GT/GS)") || (device == "stratix v (gx/gt/gs)") || (device == "StratixV(GS/GT/GX)") || (device == "STRATIXV(GS/GT/GX)") || (device == "stratixv(gs/gt/gx)") || (device == "StratixV(GS/GX/GT)") || (device == "STRATIXV(GS/GX/GT)") || (device == "stratixv(gs/gx/gt)") || (device == "StratixV(GT/GS/GX)") || (device == "STRATIXV(GT/GS/GX)") || (device == "stratixv(gt/gs/gx)") || (device == "StratixV(GT/GX/GS)") || (device == "STRATIXV(GT/GX/GS)") || (device == "stratixv(gt/gx/gs)") || (device == "StratixV(GX/GS/GT)") || (device == "STRATIXV(GX/GS/GT)") || (device == "stratixv(gx/gs/gt)") || (device == "StratixV(GX/GT/GS)") || (device == "STRATIXV(GX/GT/GS)") || (device == "stratixv(gx/gt/gs)") || (device == "Stratix V (GS/GT/GX/E)") || (device == "STRATIX V (GS/GT/GX/E)") || (device == "stratix v (gs/gt/gx/e)") || (device == "StratixV(GS/GT/GX/E)") || (device == "STRATIXV(GS/GT/GX/E)") || (device == "stratixv(gs/gt/gx/e)") || (device == "Stratix V (E)") || (device == "STRATIX V (E)") || (device == "stratix v (e)") || (device == "StratixV(E)") || (device == "STRATIXV(E)") || (device == "stratixv(e)"))
    || ((device == "Stratix") || (device == "STRATIX") || (device == "stratix") || (device == "Yeager") || (device == "YEAGER") || (device == "yeager"))
    || ((device == "eFPGA 28 HPM") || (device == "EFPGA 28 HPM") || (device == "efpga 28 hpm") || (device == "eFPGA28HPM") || (device == "EFPGA28HPM") || (device == "efpga28hpm") || (device == "Bedrock") || (device == "BEDROCK") || (device == "bedrock")))
        is_valid = 1;
    else
        is_valid = 0;

    IS_VALID_FAMILY = is_valid;
end
endfunction // IS_VALID_FAMILY


endmodule // LPM_DEVICE_FAMILIES
//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_constant
//
// Description     :  Parameterized constant generator megafunction. lpm_constant
//                    may be useful for convert a parameter into a constant.
//
// Limitation      :  n/a
//
// Results expected:  Value specified by the argument to LPM_CVALUE.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_constant (
    result // Value specified by the argument to LPM_CVALUE. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;    // Width of the result[] port. (Required)
    parameter lpm_cvalue = 0;   // Constant value to be driven out on the
                                // result[] port. (Required)
    parameter lpm_strength = "UNUSED";
    parameter lpm_type = "lpm_constant";
    parameter lpm_hint = "UNUSED";

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTERS DECLARATION
    reg[32:0] int_value;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        int_value = lpm_cvalue;
    end

// CONTINOUS ASSIGNMENT
    assign result = int_value[lpm_width-1:0];

endmodule // lpm_constant

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_inv
//
// Description     :  Parameterized inverter megafunction.
//
// Limitation      :  n/a
//
// Results expected: Inverted value of input data
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_inv (
    data,   // Data input to the lpm_inv. (Required)
    result  // inverted result. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1; // Width of the data[] and result[] ports. (Required)
    parameter lpm_type = "lpm_inv";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTERS DECLARATION
    reg    [lpm_width-1:0] result;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data)
        result = ~data;

endmodule // lpm_inv

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_and
//
// Description     :  Parameterized AND gate. This megafunction takes in data inputs
//                    for a number of AND gates.
//
// Limitation      :  n/a
//
// Results expected: Each result[] bit is the result of each AND gate.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_and (
    data,  // Data input to the AND gate. (Required)
    result // Result of the AND operators. (Required)
);

// GLOBAL PARAMETER DECLARATION
    // Width of the data[][] and result[] ports. Number of AND gates. (Required)
    parameter lpm_width = 1;
    // Number of inputs to each AND gate. Number of input buses. (Required)
    parameter lpm_size = 1;
    parameter lpm_type = "lpm_and";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [(lpm_size * lpm_width)-1:0] data;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_width-1:0] result_tmp;

// LOCAL INTEGER DECLARATION
    integer i;
    integer j;
    integer k;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_size <= 0)
        begin
            $display("Value of lpm_size parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data)
    begin
        for (i=0; i<lpm_width; i=i+1)
        begin
            result_tmp[i] = 1'b1;
            for (j=0; j<lpm_size; j=j+1)
            begin
                k = (j * lpm_width) + i;
                result_tmp[i] = result_tmp[i] & data[k];
            end
        end
    end

// CONTINOUS ASSIGNMENT
    assign result = result_tmp;
endmodule // lpm_and

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_or
//
// Description     :  Parameterized OR gate megafunction. This megafunction takes in
//                    data inputs for a number of OR gates.
//
// Limitation      :  n/a
//
// Results expected:  Each result[] bit is the result of each OR gate.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_or (
    data,  // Data input to the OR gates. (Required)
    result // Result of OR operators. (Required)
);

// GLOBAL PARAMETER DECLARATION
    // Width of the data[] and result[] ports. Number of OR gates. (Required)
    parameter lpm_width = 1;
    // Number of inputs to each OR gate. Number of input buses. (Required)
    parameter lpm_size = 1;
    parameter lpm_type = "lpm_or";
    parameter lpm_hint  = "UNUSED";

// INPUT PORT DECLARATION
    input  [(lpm_size * lpm_width)-1:0] data;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_width-1:0] result_tmp;

// LOCAL INTEGER DECLARATION
    integer i;
    integer j;
    integer k;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_size <= 0)
        begin
            $display("Value of lpm_size parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data)
    begin
        for (i=0; i<lpm_width; i=i+1)
        begin
            result_tmp[i] = 1'b0;
            for (j=0; j<lpm_size; j=j+1)
            begin
                k = (j * lpm_width) + i;
                result_tmp[i] = result_tmp[i] | data[k];
            end
        end
    end

// CONTINOUS ASSIGNMENT
    assign result = result_tmp;

endmodule // lpm_or

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_xor
//
// Description     :  Parameterized XOR gate megafunction. This megafunction takes in
//                    data inputs for a number of XOR gates.
//
// Limitation      :  n/a.
//
// Results expected:  Each result[] bit is the result of each XOR gates.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_xor (
    data,   // Data input to the XOR gates. (Required)
    result  // Result of XOR operators. (Required)
);

// GLOBAL PARAMETER DECLARATION
    // Width of the data[] and result[] ports. Number of XOR gates. (Required)
    parameter lpm_width = 1;
    // Number of inputs to each XOR gate. Number of input buses. (Required)
    parameter lpm_size = 1;
    parameter lpm_type = "lpm_xor";
    parameter lpm_hint  = "UNUSED";

// INPUT PORT DECLARATION
    input  [(lpm_size * lpm_width)-1:0] data;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_width-1:0] result_tmp;

// LOCAL INTEGER DECLARATION
    integer i;
    integer j;
    integer k;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_size <= 0)
        begin
            $display("Value of lpm_size parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data)
    begin
        for (i=0; i<lpm_width; i=i+1)
        begin
            result_tmp[i] = 1'b0;
            for (j=0; j<lpm_size; j=j+1)
            begin
                k = (j * lpm_width) + i;
                result_tmp[i] = result_tmp[i] ^ data[k];
            end
        end
    end

// CONTINOUS ASSIGNMENT
    assign result = result_tmp;

endmodule // lpm_xor

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_bustri
//
// Description     :  Parameterized tri-state buffer. lpm_bustri is useful for
//                    controlling both unidirectional and bidirectional I/O bus
//                    controllers.
//
// Limitation      :  n/a
//
// Results expected:  Belows are the three configurations which are valid:
//
//                    1) Only the input ports data[LPM_WIDTH-1..0] and enabledt are
//                       present, and only the output ports tridata[LPM_WIDTH-1..0]
//                       are present.
//
//                        ----------------------------------------------------
//                       | Input           |  Output                          |
//                       |====================================================|
//                       | enabledt        |     tridata[LPM_WIDTH-1..0]      |
//                       |----------------------------------------------------|
//                       |    0            |     Z                            |
//                       |----------------------------------------------------|
//                       |    1            |     DATA[LPM_WIDTH-1..0]         |
//                        ----------------------------------------------------
//
//                    2) Only the input ports tridata[LPM_WIDTH-1..0] and enabletr
//                       are present, and only the output ports result[LPM_WIDTH-1..0]
//                       are present.
//
//                        ----------------------------------------------------
//                       | Input           |  Output                          |
//                       |====================================================|
//                       | enabletr        |     result[LPM_WIDTH-1..0]       |
//                       |----------------------------------------------------|
//                       |    0            |     Z                            |
//                       |----------------------------------------------------|
//                       |    1            |     tridata[LPM_WIDTH-1..0]      |
//                        ----------------------------------------------------
//
//                    3) All ports are present: input ports data[LPM_WIDTH-1..0],
//                       enabledt, and enabletr; output ports result[LPM_WIDTH-1..0];
//                       and bidirectional ports tridata[LPM_WIDTH-1..0].
//
//        ----------------------------------------------------------------------------
//       |         Input        |      Bidirectional       |         Output           |
//       |----------------------------------------------------------------------------|
//       | enabledt  | enabletr | tridata[LPM_WIDTH-1..0]  |  result[LPM_WIDTH-1..0]  |
//       |============================================================================|
//       |    0      |     0    |       Z (input)          |          Z               |
//       |----------------------------------------------------------------------------|
//       |    0      |     1    |       Z (input)          |  tridata[LPM_WIDTH-1..0] |
//       |----------------------------------------------------------------------------|
//       |    1      |     0    |     data[LPM_WIDTH-1..0] |          Z               |
//       |----------------------------------------------------------------------------|
//       |    1      |     1    |     data[LPM_WIDTH-1..0] |  data[LPM_WIDTH-1..0]    |
//       ----------------------------------------------------------------------------
//
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_bustri (
    tridata,    // Bidirectional bus signal. (Required)
    data,       // Data input to the tridata[] bus. (Required)
    enabletr,   // If high, enables tridata[] onto the result bus.
    enabledt,   // If high, enables data onto the tridata[] bus.
    result      // Output from the tridata[] bus.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_type = "lpm_bustri";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  enabletr;
    input  enabledt;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INPUT/OUTPUT PORT DECLARATION
    inout  [lpm_width-1:0] tridata;

// INTERNAL REGISTERS DECLARATION
    reg  [lpm_width-1:0] result;

// INTERNAL TRI DECLARATION
    tri1  enabletr;
    tri1  enabledt;

    wire i_enabledt;
    wire i_enabletr;
    buf (i_enabledt, enabledt);
    buf (i_enabletr, enabletr);


// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data or tridata or i_enabletr or i_enabledt)
    begin
        if ((i_enabledt == 1'b0) && (i_enabletr == 1'b1))
        begin
            result = tridata;
        end
        else if ((i_enabledt == 1'b1) && (i_enabletr == 1'b1))
        begin
            result = data;
        end
        else
        begin
            result = {lpm_width{1'bz}};
        end
    end

// CONTINOUS ASSIGNMENT
    assign tridata = (i_enabledt == 1) ? data : {lpm_width{1'bz}};

endmodule // lpm_bustri

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_mux
//
// Description     :  Parameterized multiplexer megafunctions.
//
// Limitation      :  n/a
//
// Results expected:  Selected input port.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_mux (
    data,    // Data input. (Required)
    sel,     // Selects one of the input buses. (Required)
    clock,   // Clock for pipelined usage
    aclr,    // Asynchronous clear for pipelined usage.
    clken,   // Clock enable for pipelined usage.
    result   // Selected input port. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;  // Width of the data[][] and result[] ports. (Required)
    parameter lpm_size = 2;   // Number of input buses to the multiplexer. (Required)
    parameter lpm_widths = 1; // Width of the sel[] input port. (Required)
    parameter lpm_pipeline = 0; // Specifies the number of Clock cycles of latency
                                // associated with the result[] output.
    parameter lpm_type = "lpm_mux";
    parameter lpm_hint  = "UNUSED";

// INPUT PORT DECLARATION
    input [(lpm_size * lpm_width)-1:0] data;
    input [lpm_widths-1:0] sel;
    input clock;
    input aclr;
    input clken;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_width-1:0] result_pipe [lpm_pipeline+1:0];
    reg [lpm_width-1:0] tmp_result;

// LOCAL INTEGER DECLARATION
    integer i;
    integer pipe_ptr;

// INTERNAL TRI DECLARATION
    tri0 aclr;
    tri0 clock;
    tri1 clken;

    wire i_aclr;
    wire i_clock;
    wire i_clken;
    buf (i_aclr, aclr);
    buf (i_clock, clock);
    buf (i_clken, clken);

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_size <= 1)
        begin
            $display("Value of lpm_size parameter must be greater than 1 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_widths <= 0)
        begin
            $display("Value of lpm_widths parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_pipeline < 0)
        begin
            $display("Value of lpm_pipeline parameter must NOT less than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        pipe_ptr = 0;
    end


// ALWAYS CONSTRUCT BLOCK
    always @(data or sel)
    begin
        tmp_result = 0;

        if (sel < lpm_size)
        begin
            for (i = 0; i < lpm_width; i = i + 1)
                tmp_result[i] = data[(sel * lpm_width) + i];
        end
        else
            tmp_result = {lpm_width{1'bx}};
    end

    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr)
        begin
            for (i = 0; i <= (lpm_pipeline+1); i = i + 1)
                result_pipe[i] <= 1'b0;
            pipe_ptr <= 0;
        end
        else if (i_clken == 1'b1)
        begin
            result_pipe[pipe_ptr] <= tmp_result;

            if (lpm_pipeline > 1)
                pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
        end
    end

// CONTINOUS ASSIGNMENT
    assign result = (lpm_pipeline > 0) ? result_pipe[pipe_ptr] : tmp_result;

endmodule // lpm_mux
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_decode
//
// Description     :  Parameterized decoder megafunction.
//
// Limitation      :  n/a
//
// Results expected:  Decoded output.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_decode (
    data,    // Data input. Treated as an unsigned binary encoded number. (Required)
    enable,  // Enable. All outputs low when not active.
    clock,   // Clock for pipelined usage.
    aclr,    // Asynchronous clear for pipelined usage.
    clken,   // Clock enable for pipelined usage.
    eq       // Decoded output. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;                // Width of the data[] port, or the
                                            // input value to be decoded. (Required)
    parameter lpm_decodes = 1 << lpm_width; // Number of explicit decoder outputs. (Required)
    parameter lpm_pipeline = 0;             // Number of Clock cycles of latency
    parameter lpm_type = "lpm_decode";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  enable;
    input  clock;
    input  aclr;
    input  clken;

// OUTPUT PORT DECLARATION
    output [lpm_decodes-1:0] eq;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_decodes-1:0] eq_pipe [(lpm_pipeline+1):0];
    reg    [lpm_decodes-1:0] tmp_eq;

// LOCAL INTEGER DECLARATION
    integer i;
    integer pipe_ptr;

// INTERNAL TRI DECLARATION
    tri1   enable;
    tri0   clock;
    tri0   aclr;
    tri1   clken;

    wire i_clock;
    wire i_clken;
    wire i_aclr;
    wire i_enable;
    buf (i_clock, clock);
    buf (i_clken, clken);
    buf (i_aclr, aclr);
    buf (i_enable, enable);

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (lpm_decodes <= 0)
        begin
            $display("Value of lpm_decodes parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (lpm_decodes > (1 << lpm_width))
        begin
            $display("Value of lpm_decodes parameter must be less or equal to 2^lpm_width (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (lpm_pipeline < 0)
        begin
            $display("Value of lpm_pipeline parameter must be greater or equal to 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        pipe_ptr = 0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data or i_enable)
    begin
        tmp_eq = {lpm_decodes{1'b0}};
        if (i_enable)
            tmp_eq[data] = 1'b1;
    end

    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr)
        begin
            for (i = 0; i <= lpm_pipeline; i = i + 1)
                eq_pipe[i] <= {lpm_decodes{1'b0}};

            pipe_ptr <= 0;
        end
        else if (clken == 1'b1)
        begin
            eq_pipe[pipe_ptr] <= tmp_eq;

            if (lpm_pipeline > 1)
                pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
        end
    end

    assign eq = (lpm_pipeline > 0) ? eq_pipe[pipe_ptr] : tmp_eq;

endmodule // lpm_decode
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_clshift
//
// Description     :  Parameterized combinatorial logic shifter or barrel shifter
//                    megafunction.
//
// Limitation      :  n/a
//
// Results expected:  Return the shifted data and underflow/overflow status bit.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_clshift (
    data,       // Data to be shifted. (Required)
    distance,   // Number of positions to shift data[] in the direction specified
                // by the direction port. (Required)
    direction,  // Direction of shift. Low = left (toward the MSB),
                //                     high = right (toward the LSB).
    clock,      // Clock for pipelined usage.
    aclr,       // Asynchronous clear for pipelined usage.
    clken,      // Clock enable for pipelined usage.
    result,     // Shifted data. (Required)
    underflow,  // Logical or arithmetic underflow.
    overflow    // Logical or arithmetic overflow.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;    // Width of the data[] and result[] ports. Must be
                                // greater than 0 (Required)
    parameter lpm_widthdist = 1; // Width of the distance[] input port. (Required)
    parameter lpm_shifttype = "LOGICAL"; // Type of shifting operation to be performed.
    parameter lpm_pipeline = 0;             // Number of Clock cycles of latency
    parameter lpm_type = "lpm_clshift";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  [lpm_widthdist-1:0] distance;
    input  direction;
    input  clock;
    input  aclr;
    input  clken;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;
    output underflow;
    output overflow;

// INTERNAL REGISTERS DECLARATION
    reg    [lpm_width-1:0] ONES;
    reg    [lpm_width-1:0] ZEROS;
    reg    [lpm_width-1:0] tmp_result;
    reg    tmp_underflow;
    reg    tmp_overflow;
    reg    [lpm_width-1:0] result_pipe [(lpm_pipeline+1):0];
    reg    [(lpm_pipeline+1):0] overflow_pipe;
    reg    [(lpm_pipeline+1):0] underflow_pipe;

// LOCAL INTEGER DECLARATION
    integer i;
    integer i1;
    integer pipe_ptr;

// INTERNAL TRI DECLARATION
    tri0  direction;
    tri0   clock;
    tri0   aclr;
    tri1   clken;

    wire i_direction;
    wire i_clock;
    wire i_clken;
    wire i_aclr;
    buf (i_direction, direction);
    buf (i_clock, clock);
    buf (i_clken, clken);
    buf (i_aclr, aclr);


// FUNCTON DECLARATION
    // Perform logival shift operation
    function [lpm_width+1:0] LogicShift;
        input [lpm_width-1:0] data;
        input [lpm_widthdist-1:0] shift_num;
        input direction;
        reg   [lpm_width-1:0] tmp_buf;
        reg   underflow;
        reg   overflow;

        begin
            tmp_buf = data;
            overflow = 1'b0;
            underflow = 1'b0;
            if ((direction) && (shift_num > 0)) // shift right
            begin
                tmp_buf = data >> shift_num;
                if ((data != ZEROS) && ((shift_num >= lpm_width) || (tmp_buf == ZEROS)))
                    underflow = 1'b1;
            end
            else if (shift_num > 0) // shift left
            begin
                tmp_buf = data << shift_num;
                if ((data != ZEROS) && ((shift_num >= lpm_width)
                    || ((data >> (lpm_width-shift_num)) != ZEROS)))
                    overflow = 1'b1;
            end
            LogicShift = {overflow,underflow,tmp_buf[lpm_width-1:0]};
        end
    endfunction // LogicShift

    // Perform Arithmetic shift operation
    function [lpm_width+1:0] ArithShift;
        input [lpm_width-1:0] data;
        input [lpm_widthdist-1:0] shift_num;
        input direction;
        reg   [lpm_width-1:0] tmp_buf;
        reg   underflow;
        reg   overflow;
        integer i;
        integer i1;

        begin
            tmp_buf = data;
            overflow = 1'b0;
            underflow = 1'b0;

            if (shift_num < lpm_width)
            begin
                if ((direction) && (shift_num > 0))   // shift right
                begin
                    if (data[lpm_width-1] == 1'b0) // positive number
                    begin
                        tmp_buf = data >> shift_num;
                        if ((data != ZEROS) && ((shift_num >= lpm_width) || (tmp_buf == ZEROS)))
                            underflow = 1'b1;
                    end
                    else // negative number
                    begin
                        tmp_buf = (data >> shift_num) | (ONES << (lpm_width - shift_num));
                        if ((data != ONES) && ((shift_num >= lpm_width-1) || (tmp_buf == ONES)))
                            underflow = 1'b1;
                    end
                end
                else if (shift_num > 0) // shift left
                begin
                    tmp_buf = data << shift_num;

                    for (i=lpm_width-1; i >= lpm_width-shift_num; i=i-1)
                    begin
                        if(data[i-1] != data[lpm_width-1])
                            overflow = 1'b1;
                    end
                end
            end
            else    // shift_num >= lpm_width
            begin
                if (direction)
                begin
                    for (i=0; i < lpm_width; i=i+1)
                        tmp_buf[i] = data[lpm_width-1];

                    underflow = 1'b1;
                end
                else
                begin
                    tmp_buf = {lpm_width{1'b0}};

                    if (data != ZEROS)
                    begin
                        overflow = 1'b1;
                    end
                end
            end
            ArithShift = {overflow,underflow,tmp_buf[lpm_width-1:0]};
        end
    endfunction // ArithShift

    // Perform rotate shift operation
    function [lpm_width+1:0] RotateShift;
        input [lpm_width-1:0] data;
        input [lpm_widthdist-1:0] shift_num;
        input direction;
        reg   [lpm_width-1:0] tmp_buf;

        begin
            tmp_buf = data;
            if ((direction) && (shift_num > 0)) // shift right
                tmp_buf = (data >> shift_num) | (data << (lpm_width - shift_num));
            else if (shift_num > 0) // shift left
                tmp_buf = (data << shift_num) | (data >> (lpm_width - shift_num));
            RotateShift = {2'bx, tmp_buf[lpm_width-1:0]};
        end
    endfunction // RotateShift

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if ((lpm_shifttype != "LOGICAL") &&
            (lpm_shifttype != "ARITHMETIC") &&
            (lpm_shifttype != "ROTATE") &&
            (lpm_shifttype != "UNUSED"))          // non-LPM 220 standard
            begin
                $display("Error!  LPM_SHIFTTYPE value must be \"LOGICAL\", \"ARITHMETIC\", or \"ROTATE\".");
                $display("Time: %0t  Instance: %m", $time);
            end

        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_widthdist <= 0)
        begin
            $display("Value of lpm_widthdist parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        for (i=0; i < lpm_width; i=i+1)
        begin
            ONES[i] = 1'b1;
            ZEROS[i] = 1'b0;
        end

        for (i = 0; i <= lpm_pipeline; i = i + 1)
        begin
            result_pipe[i] = ZEROS;
            overflow_pipe[i] = 1'b0;
            underflow_pipe[i] = 1'b0;
        end

        tmp_result = ZEROS;
        tmp_underflow = 1'b0;
        tmp_overflow = 1'b0;
        pipe_ptr = 0;

    end

// ALWAYS CONSTRUCT BLOCK
    always @(data or i_direction or distance)
    begin
        if ((lpm_shifttype == "LOGICAL") || (lpm_shifttype == "UNUSED"))
            {tmp_overflow, tmp_underflow, tmp_result} = LogicShift(data, distance, i_direction);
        else if (lpm_shifttype == "ARITHMETIC")
            {tmp_overflow, tmp_underflow, tmp_result} = ArithShift(data, distance, i_direction);
        else if (lpm_shifttype == "ROTATE")
            {tmp_overflow, tmp_underflow, tmp_result} = RotateShift(data, distance, i_direction);
    end

    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr)
        begin
            for (i1 = 0; i1 <= lpm_pipeline; i1 = i1 + 1)
            begin
                result_pipe[i1] <= {lpm_width{1'b0}};
                overflow_pipe[i1] <= 1'b0;
                underflow_pipe[i1] <= 1'b0;
            end
            pipe_ptr <= 0;
        end
        else if (i_clken == 1'b1)
        begin
            result_pipe[pipe_ptr] <= tmp_result;
            overflow_pipe[pipe_ptr] <= tmp_overflow;
            underflow_pipe[pipe_ptr] <= tmp_underflow;

            if (lpm_pipeline > 1)
                pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
        end
    end

    assign result = (lpm_pipeline > 0) ? result_pipe[pipe_ptr] : tmp_result;
    assign overflow = (lpm_pipeline > 0) ? overflow_pipe[pipe_ptr] : tmp_overflow;
    assign underflow = (lpm_pipeline > 0) ? underflow_pipe[pipe_ptr] : tmp_underflow;

endmodule // lpm_clshift
//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_add_sub
//
// Description     :  Parameterized adder/subtractor megafunction.
//
// Limitation      :  n/a
//
// Results expected:  If performs as adder, the result will be dataa[]+datab[]+cin.
//                    If performs as subtractor, the result will be dataa[]-datab[]+cin-1.
//                    Also returns carry out bit and overflow status bit.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_add_sub (
    dataa,      // Augend/Minuend
    datab,      // Addend/Subtrahend
    cin,        // Carry-in to the low-order bit.
    add_sub,    // If the signal is high, the operation = dataa[]+datab[]+cin.
                // If the signal is low, the operation = dataa[]-datab[]+cin-1.

    clock,      // Clock for pipelined usage.
    aclr,       // Asynchronous clear for pipelined usage.
    clken,      // Clock enable for pipelined usage.
    result,     // dataa[]+datab[]+cin or dataa[]-datab[]+cin-1
    cout,       // Carry-out (borrow-in) of the MSB.
    overflow    // Result exceeds available precision.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1; // Width of the dataa[],datab[], and result[] ports.
    parameter lpm_representation = "SIGNED"; // Type of addition performed
    parameter lpm_direction  = "UNUSED";  // Specify the operation of the lpm_add_sub function
    parameter lpm_pipeline = 0; // Number of Clock cycles of latency
    parameter lpm_type = "lpm_add_sub";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] dataa;
    input  [lpm_width-1:0] datab;
    input  cin;
    input  add_sub;
    input  clock;
    input  aclr;
    input  clken;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;
    output cout;
    output overflow;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_width-1:0] result_pipe [(lpm_pipeline+1):0];
    reg [(lpm_pipeline+1):0] cout_pipe;
    reg [(lpm_pipeline+1):0] overflow_pipe;
    reg tmp_cout;
    reg tmp_overflow;
    reg [lpm_width-1:0] tmp_result;
    reg i_cin;

// LOCAL INTEGER DECLARATION
    integer borrow;
    integer i;
    integer pipe_ptr;

// INTERNAL TRI DECLARATION
    tri1 i_add_sub;
    tri0 i_aclr;
    tri1 i_clken;
    tri0 i_clock;


// INITIAL CONSTRUCT BLOCK
    initial
    begin
        // check if lpm_width < 0
        if (lpm_width <= 0)
        begin
            $display("Error!  LPM_WIDTH must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if ((lpm_direction != "ADD") &&
            (lpm_direction != "SUB") &&
            (lpm_direction != "UNUSED") &&   // non-LPM 220 standard
            (lpm_direction != "DEFAULT"))    // non-LPM 220 standard
        begin
            $display("Error!  LPM_DIRECTION value must be \"ADD\" or \"SUB\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if ((lpm_representation != "SIGNED") &&
            (lpm_representation != "UNSIGNED"))
        begin
            $display("Error!  LPM_REPRESENTATION value must be \"SIGNED\" or \"UNSIGNED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (lpm_pipeline < 0)
        begin
            $display("Error!  LPM_PIPELINE must be greater than or equal to 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        for (i = 0; i <= (lpm_pipeline+1); i = i + 1)
        begin
            result_pipe[i] = 'b0;
            cout_pipe[i] = 1'b0;
            overflow_pipe[i] = 1'b0;
        end

        pipe_ptr = 0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(cin or dataa or datab or i_add_sub)
    begin
        i_cin = 1'b0;
        borrow = 1'b0;

        // cout is the same for both signed and unsign representation.
        if ((lpm_direction == "ADD") || ((i_add_sub == 1) &&
            ((lpm_direction == "UNUSED") || (lpm_direction == "DEFAULT")) ))
        begin
            i_cin = (cin === 1'bz) ? 0 : cin;
            {tmp_cout, tmp_result} = dataa + datab + i_cin;
            tmp_overflow = tmp_cout;
        end
        else if ((lpm_direction == "SUB") || ((i_add_sub == 0) &&
                ((lpm_direction == "UNUSED") || (lpm_direction == "DEFAULT")) ))
        begin
            i_cin = (cin === 1'bz) ? 1 : cin;
            borrow = (~i_cin) ? 1 : 0;
            {tmp_overflow, tmp_result} = dataa - datab - borrow;
            tmp_cout = (dataa >= (datab+borrow))?1:0;
        end

        if (lpm_representation == "SIGNED")
        begin
            // perform the addtion or subtraction operation
            if ((lpm_direction == "ADD") || ((i_add_sub == 1) &&
                ((lpm_direction == "UNUSED") || (lpm_direction == "DEFAULT")) ))
            begin
                tmp_result = dataa + datab + i_cin;
                tmp_overflow = ((dataa[lpm_width-1] == datab[lpm_width-1]) &&
                                                (dataa[lpm_width-1] != tmp_result[lpm_width-1])) ?
                                                1 : 0;
            end
            else if ((lpm_direction == "SUB") || ((i_add_sub == 0) &&
                    ((lpm_direction == "UNUSED") || (lpm_direction == "DEFAULT")) ))
            begin
                tmp_result = dataa - datab - borrow;
                tmp_overflow = ((dataa[lpm_width-1] != datab[lpm_width-1]) &&
                                                (dataa[lpm_width-1] != tmp_result[lpm_width-1])) ?
                                                1 : 0;
            end
        end
    end

    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr)
        begin
            for (i = 0; i <= (lpm_pipeline+1); i = i + 1)
            begin
                result_pipe[i] <= {lpm_width{1'b0}};
                cout_pipe[i] <= 1'b0;
                overflow_pipe[i] <= 1'b0;
            end
            pipe_ptr <= 0;
        end
        else if (i_clken == 1)
        begin
            result_pipe[pipe_ptr] <= tmp_result;
            cout_pipe[pipe_ptr] <= tmp_cout;
            overflow_pipe[pipe_ptr] <= tmp_overflow;

            if (lpm_pipeline > 1)
                pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
        end
    end

// CONTINOUS ASSIGNMENT
    assign result = (lpm_pipeline > 0) ? result_pipe[pipe_ptr] : tmp_result;
    assign cout = (lpm_pipeline > 0) ? cout_pipe[pipe_ptr] : tmp_cout;
    assign overflow = (lpm_pipeline > 0) ? overflow_pipe[pipe_ptr] : tmp_overflow;
    assign i_clock = clock;
    assign i_aclr = aclr;
    assign i_clken = clken;
    assign i_add_sub = add_sub;

endmodule // lpm_add_sub
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_compare
//
// Description     :  Parameterized comparator megafunction. The comparator will
//                    compare between data[] and datab[] and return the status of
//                    comparation for the following operation.
//                    1) dataa[] < datab[].
//                    2) dataa[] == datab[].
//                    3) dataa[] > datab[].
//                    4) dataa[] >= datab[].
//                    5) dataa[] != datab[].
//                    6) dataa[] <= datab[].
//
// Limitation      :  n/a
//
// Results expected:  Return status bits of the comparision between dataa[] and
//                    datab[].
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_compare (
    dataa,   // Value to be compared to datab[]. (Required)
    datab,   // Value to be compared to dataa[]. (Required)
    clock,   // Clock for pipelined usage.
    aclr,    // Asynchronous clear for pipelined usage.
    clken,   // Clock enable for pipelined usage.

    // One of the following ports must be present.
    alb,     // High (1) if dataa[] < datab[].
    aeb,     // High (1) if dataa[] == datab[].
    agb,     // High (1) if dataa[] > datab[].
    aleb,    // High (1) if dataa[] <= datab[].
    aneb,    // High (1) if dataa[] != datab[].
    ageb     // High (1) if dataa[] >= datab[].
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;  // Width of the dataa[] and datab[] ports. (Required)
    parameter lpm_representation = "UNSIGNED";  // Type of comparison performed:
                                                // "SIGNED", "UNSIGNED"
    parameter lpm_pipeline = 0; // Specifies the number of Clock cycles of latency
                                // associated with the alb, aeb, agb, ageb, aleb,
                                //  or aneb output.
    parameter lpm_type = "lpm_compare";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] dataa;
    input  [lpm_width-1:0] datab;
    input  clock;
    input  aclr;
    input  clken;

// OUTPUT PORT DECLARATION
    output alb;
    output aeb;
    output agb;
    output aleb;
    output aneb;
    output ageb;

// INTERNAL REGISTERS DECLARATION
    reg [lpm_pipeline+1:0] alb_pipe;
    reg [lpm_pipeline+1:0] aeb_pipe;
    reg [lpm_pipeline+1:0] agb_pipe;
    reg [lpm_pipeline+1:0] aleb_pipe;
    reg [lpm_pipeline+1:0] aneb_pipe;
    reg [lpm_pipeline+1:0] ageb_pipe;
    reg tmp_alb;
    reg tmp_aeb;
    reg tmp_agb;
    reg tmp_aleb;
    reg tmp_aneb;
    reg tmp_ageb;


// LOCAL INTEGER DECLARATION
    integer i;
    integer pipe_ptr;

// INTERNAL TRI DECLARATION
    tri0 aclr;
    tri0 clock;
    tri1 clken;

    wire i_aclr;
    wire i_clock;
    wire i_clken;
    buf (i_aclr, aclr);
    buf (i_clock, clock);
    buf (i_clken, clken);

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if ((lpm_representation != "SIGNED") &&
            (lpm_representation != "UNSIGNED"))
        begin
            $display("Error!  LPM_REPRESENTATION value must be \"SIGNED\" or \"UNSIGNED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        pipe_ptr = 0;
    end

// ALWAYS CONSTRUCT BLOCK
    // get the status of comparison
    always @(dataa or datab)
    begin
        tmp_aeb = (dataa == datab);
        tmp_aneb = (dataa != datab);

        if ((lpm_representation == "SIGNED") &&
            ((dataa[lpm_width-1] ^ datab[lpm_width-1]) == 1))
        begin
            // create latency
            tmp_alb = (dataa > datab);
            tmp_agb = (dataa < datab);
            tmp_aleb = (dataa >= datab);
            tmp_ageb = (dataa <= datab);
        end
        else
        begin
        // create latency
            tmp_alb = (dataa < datab);
            tmp_agb = (dataa > datab);
            tmp_aleb = (dataa <= datab);
            tmp_ageb = (dataa >= datab);
        end
    end

    // pipelining process
    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr) // reset all variables
        begin
            for (i = 0; i <= (lpm_pipeline + 1); i = i + 1)
            begin
                aeb_pipe[i] <= 1'b0;
                agb_pipe[i] <= 1'b0;
                alb_pipe[i] <= 1'b0;
                aleb_pipe[i] <= 1'b0;
                aneb_pipe[i] <= 1'b0;
                ageb_pipe[i] <= 1'b0;
            end
            pipe_ptr <= 0;
        end
        else if (i_clken == 1)
        begin
            alb_pipe[pipe_ptr] <= tmp_alb;
            aeb_pipe[pipe_ptr] <= tmp_aeb;
            agb_pipe[pipe_ptr] <= tmp_agb;
            aleb_pipe[pipe_ptr] <= tmp_aleb;
            aneb_pipe[pipe_ptr] <= tmp_aneb;
            ageb_pipe[pipe_ptr] <= tmp_ageb;

            if (lpm_pipeline > 1)
                pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
        end
    end

// CONTINOUS ASSIGNMENT
    assign alb = (lpm_pipeline > 0) ? alb_pipe[pipe_ptr] : tmp_alb;
    assign aeb = (lpm_pipeline > 0) ? aeb_pipe[pipe_ptr] : tmp_aeb;
    assign agb = (lpm_pipeline > 0) ? agb_pipe[pipe_ptr] : tmp_agb;
    assign aleb = (lpm_pipeline > 0) ? aleb_pipe[pipe_ptr] : tmp_aleb;
    assign aneb = (lpm_pipeline > 0) ? aneb_pipe[pipe_ptr] : tmp_aneb;
    assign ageb = (lpm_pipeline > 0) ? ageb_pipe[pipe_ptr] : tmp_ageb;

endmodule // lpm_compare

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_mult
//
// Description     :  Parameterized multiplier megafunction.
//
// Limitation      :  n/a
//
// Results expected:  dataa[] * datab[] + sum[].
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_mult (
    dataa,  // Multiplicand. (Required)
    datab,  // Multiplier. (Required)
    sum,    // Partial sum.
    aclr,   // Asynchronous clear for pipelined usage.
    sclr,   // Synchronous clear for pipelined usage.
    clock,  // Clock for pipelined usage.
    clken,  // Clock enable for pipelined usage.
    result  // result = dataa[] * datab[] + sum. The product LSB is aligned with the sum LSB.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_widtha = 1; // Width of the dataa[] port. (Required)
    parameter lpm_widthb = 1; // Width of the datab[] port. (Required)
    parameter lpm_widthp = 1; // Width of the result[] port. (Required)
    parameter lpm_widths = 1; // Width of the sum[] port. (Required)
    parameter lpm_representation  = "UNSIGNED"; // Type of multiplication performed
    parameter lpm_pipeline  = 0; // Number of clock cycles of latency
    parameter lpm_type = "lpm_mult";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_widtha-1:0] dataa;
    input  [lpm_widthb-1:0] datab;
    input  [lpm_widths-1:0] sum;
    input  aclr;
    input  sclr;
    input  clock;
    input  clken;

// OUTPUT PORT DECLARATION
    output [lpm_widthp-1:0] result;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_widthp-1:0] result_pipe [lpm_pipeline+1:0];
    reg [lpm_widthp-1:0] i_prod;
    reg [lpm_widthp-1:0] t_p;
    reg [lpm_widths-1:0] i_prod_s;
    reg [lpm_widths-1:0] t_s;
    reg [lpm_widtha+lpm_widthb-1:0] i_prod_ab;
    reg [lpm_widtha-1:0] t_a;
    reg [lpm_widthb-1:0] t_b;
    reg sign_ab;
    reg sign_s;
    reg [8*5:1] input_a_is_constant;
    reg [8*5:1] input_b_is_constant;
    reg [8*lpm_widtha:1] input_a_fixed_value;
    reg [8*lpm_widthb:1] input_b_fixed_value;
    reg [lpm_widtha-1:0] dataa_fixed;
    reg [lpm_widthb-1:0] datab_fixed;


// LOCAL INTEGER DECLARATION
    integer i;
    integer pipe_ptr;

// INTERNAL WIRE DECLARATION
    wire [lpm_widtha-1:0] dataa_wire;
    wire [lpm_widthb-1:0] datab_wire;

// INTERNAL TRI DECLARATION
    tri0 aclr;
    tri0 sclr;
    tri0 clock;
    tri1 clken;

    wire i_aclr;
    wire i_sclr;
    wire i_clock;
    wire i_clken;
    buf (i_aclr, aclr);
    buf (i_sclr, sclr);
    buf (i_clock, clock);
    buf (i_clken, clken);

// COMPONENT INSTANTIATIONS
    LPM_HINT_EVALUATION eva();

// FUNCTION DECLARATION
    // convert string to binary bits.
    function integer str2bin;
    input [8*256:1] str;
    input str_width;

    reg [8*256:1] reg_str;
    reg [255:0] bin;
    reg [8:1] tmp;
    integer m;
    integer str_width;

    begin
        reg_str = str;
        for (m=0; m < str_width; m=m+1)
        begin
            tmp = reg_str[8:1];
            reg_str = reg_str >> 8;

            case (tmp)
                "0"    : bin[m] = 1'b0;
                "1"    : bin[m] = 1'b1;
                default: bin[m] = 1'bx;
            endcase
        end
        str2bin = bin;
    end
    endfunction

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        // check if lpm_widtha > 0
        if (lpm_widtha <= 0)
        begin
            $display("Error!  lpm_widtha must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check if lpm_widthb > 0
        if (lpm_widthb <= 0)
        begin
            $display("Error!  lpm_widthb must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check if lpm_widthp > 0
        if (lpm_widthp <= 0)
        begin
            $display("Error!  lpm_widthp must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check if lpm_widthp > 0
        if (lpm_widths <= 0)
        begin
            $display("Error!  lpm_widths must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check for valid lpm_rep value
        if ((lpm_representation != "SIGNED") && (lpm_representation != "UNSIGNED"))
        begin
            $display("Error!  lpm_representation value must be \"SIGNED\" or \"UNSIGNED\".", $time);
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        input_a_is_constant = eva.GET_PARAMETER_VALUE(lpm_hint, "INPUT_A_IS_CONSTANT");

        if (input_a_is_constant == "FIXED")
        begin
            input_a_fixed_value = eva.GET_PARAMETER_VALUE(lpm_hint, "INPUT_A_FIXED_VALUE");
            dataa_fixed = str2bin(input_a_fixed_value, lpm_widtha);
        end

        input_b_is_constant = eva.GET_PARAMETER_VALUE(lpm_hint, "INPUT_B_IS_CONSTANT");

        if (input_b_is_constant == "FIXED")
        begin
            input_b_fixed_value = eva.GET_PARAMETER_VALUE(lpm_hint, "INPUT_B_FIXED_VALUE");
            datab_fixed = str2bin(input_b_fixed_value, lpm_widthb);
        end

        pipe_ptr = 0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(dataa_wire or datab_wire or sum)
    begin
        t_a = dataa_wire;
        t_b = datab_wire;
        t_s = sum;
        sign_ab = 1'b0;
        sign_s = 1'b0;

        // if inputs are sign number
        if (lpm_representation == "SIGNED")
        begin
            sign_ab = dataa_wire[lpm_widtha-1] ^ datab_wire[lpm_widthb-1];
            sign_s = sum[lpm_widths-1];

            // if negative number, represent them as 2 compliment number.
            if (dataa_wire[lpm_widtha-1] == 1)
                t_a = (~dataa_wire) + 1;
            if (datab_wire[lpm_widthb-1] == 1)
                t_b = (~datab_wire) + 1;
            if (sum[lpm_widths-1] == 1)
                t_s = (~sum) + 1;
        end

        // if sum port is not used
        if (sum === {lpm_widths{1'bz}})
        begin
            t_s = {lpm_widths{1'b0}};
            sign_s = 1'b0;
        end

        if (sign_ab == sign_s)
        begin
            i_prod = (t_a * t_b) + t_s;
            i_prod_s = (t_a * t_b) + t_s;
            i_prod_ab = (t_a * t_b) + t_s;
        end
        else
        begin
            i_prod = (t_a * t_b) - t_s;
            i_prod_s = (t_a * t_b) - t_s;
            i_prod_ab = (t_a * t_b) - t_s;
        end

        // if dataa[] * datab[] produces negative number, compliment the result
        if (sign_ab)
        begin
            i_prod = (~i_prod) + 1;
            i_prod_s = (~i_prod_s) + 1;
            i_prod_ab = (~i_prod_ab) + 1;
        end

        if ((lpm_widthp < lpm_widths) || (lpm_widthp < (lpm_widtha+lpm_widthb)))
            for (i = 0; i < lpm_widthp; i = i + 1)
                i_prod[lpm_widthp-1-i] = (lpm_widths > lpm_widtha+lpm_widthb)
                                            ? i_prod_s[lpm_widths-1-i]
                                            : i_prod_ab[lpm_widtha+lpm_widthb-1-i];

    end

    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr) // clear the pipeline for result to 0
        begin
            for (i = 0; i <= (lpm_pipeline + 1); i = i + 1)
                result_pipe[i] <= {lpm_widthp{1'b0}};

            pipe_ptr <= 0;
        end
        else if (i_clken == 1)
        begin
            if(i_sclr)
            begin
                for (i = 0; i <= (lpm_pipeline + 1); i = i + 1)
                result_pipe[i] <= {lpm_widthp{1'b0}};

                pipe_ptr <= 0;
            end
            else
            begin
                result_pipe[pipe_ptr] <= i_prod;

                if (lpm_pipeline > 1)
                    pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
            end
        end
    end

// CONTINOUS ASSIGNMENT
    assign dataa_wire =  (input_a_is_constant == "FIXED") ? dataa_fixed : dataa;
    assign datab_wire =  (input_b_is_constant == "FIXED") ? datab_fixed : datab;
    assign result = (lpm_pipeline > 0) ? result_pipe[pipe_ptr] : i_prod;

endmodule // lpm_mult
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_divide
//
// Description     :  Parameterized divider megafunction. This function performs a
//                    divide operation such that denom * quotient + remain = numer
//                    The function allows for all combinations of signed(two's
//                    complement) and unsigned inputs. If any of the inputs is
//                    signed, the output is signed. Otherwise the output is unsigned.
//                    The function also allows the remainder to be specified as
//                    always positive (in which case remain >= 0); otherwise remain
//                    is zero or the same sign as the numerator
//                    (this parameter is ignored in the case of purely unsigned
//                    division). Finally the function is also pipelinable.
//
// Limitation      :  n/a
//
// Results expected:  Return quotient and remainder.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_divide (
    numer,  // The numerator (Required)
    denom,  // The denominator (Required)
    clock,  // Clock input for pipelined usage
    aclr,   // Asynchronous clear signal
    clken,  // Clock enable for pipelined usage.
    quotient, // Quotient (Required)
    remain    // Remainder (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_widthn = 1;  // Width of the numer[] and quotient[] port. (Required)
    parameter lpm_widthd = 1;  // Width of the denom[] and remain[] port. (Required)
    parameter lpm_nrepresentation = "UNSIGNED";  // The representation of numer
    parameter lpm_drepresentation = "UNSIGNED";  // The representation of denom
    parameter lpm_pipeline = 0; // Number of Clock cycles of latency
    parameter lpm_type = "lpm_divide";
    parameter lpm_hint = "LPM_REMAINDERPOSITIVE=TRUE";

// INPUT PORT DECLARATION
    input  [lpm_widthn-1:0] numer;
    input  [lpm_widthd-1:0] denom;
    input  clock;
    input  aclr;
    input  clken;

// OUTPUT PORT DECLARATION
    output [lpm_widthn-1:0] quotient;
    output [lpm_widthd-1:0] remain;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_widthn-1:0] quotient_pipe [lpm_pipeline+1:0];
    reg [lpm_widthd-1:0] remain_pipe [lpm_pipeline+1:0];
    reg [lpm_widthn-1:0] tmp_quotient;
    reg [lpm_widthd-1:0] tmp_remain;
    reg [lpm_widthn-1:0] not_numer;
    reg [lpm_widthn-1:0] int_numer;
    reg [lpm_widthd-1:0] not_denom;
    reg [lpm_widthd-1:0] int_denom;
    reg [lpm_widthn-1:0] t_numer;
    reg [lpm_widthn-1:0] t_q;
    reg [lpm_widthd-1:0] t_denom;
    reg [lpm_widthd-1:0] t_r;
    reg sign_q;
    reg sign_r;
    reg sign_n;
    reg sign_d;
    reg [8*5:1] lpm_remainderpositive;


// LOCAL INTEGER DECLARATION
    integer i;
    integer rsig;
    integer pipe_ptr;

// INTERNAL TRI DECLARATION
    tri0 aclr;
    tri0 clock;
    tri1 clken;

    wire i_aclr;
    wire i_clock;
    wire i_clken;
    buf (i_aclr, aclr);
    buf (i_clock, clock);
    buf (i_clken, clken);

// COMPONENT INSTANTIATIONS
    LPM_HINT_EVALUATION eva();

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        // check if lpm_widthn > 0
        if (lpm_widthn <= 0)
        begin
            $display("Error!  LPM_WIDTHN must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check if lpm_widthd > 0
        if (lpm_widthd <= 0)
        begin
            $display("Error!  LPM_WIDTHD must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check for valid lpm_nrepresentation value
        if ((lpm_nrepresentation != "SIGNED") && (lpm_nrepresentation != "UNSIGNED"))
        begin
            $display("Error!  LPM_NREPRESENTATION value must be \"SIGNED\" or \"UNSIGNED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check for valid lpm_drepresentation value
        if ((lpm_drepresentation != "SIGNED") && (lpm_drepresentation != "UNSIGNED"))
        begin
            $display("Error!  LPM_DREPRESENTATION value must be \"SIGNED\" or \"UNSIGNED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check for valid lpm_remainderpositive value
        lpm_remainderpositive = eva.GET_PARAMETER_VALUE(lpm_hint, "LPM_REMAINDERPOSITIVE");
        if ((lpm_remainderpositive == "TRUE") &&
            (lpm_remainderpositive == "FALSE"))
        begin
            $display("Error!  LPM_REMAINDERPOSITIVE value must be \"TRUE\" or \"FALSE\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        for (i = 0; i <= (lpm_pipeline+1); i = i + 1)
        begin
            quotient_pipe[i] <= {lpm_widthn{1'b0}};
            remain_pipe[i] <= {lpm_widthd{1'b0}};
        end

        pipe_ptr = 0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(numer or denom or lpm_remainderpositive)
    begin
        sign_q = 1'b0;
        sign_r = 1'b0;
        sign_n = 1'b0;
        sign_d = 1'b0;
        t_numer = numer;
        t_denom = denom;

        if (lpm_nrepresentation == "SIGNED")
            if (numer[lpm_widthn-1] == 1'b1)
            begin
                t_numer = ~numer + 1;  // numer is negative number
                sign_n = 1'b1;
            end

        if (lpm_drepresentation == "SIGNED")
            if (denom[lpm_widthd-1] == 1'b1)
            begin
                t_denom = ~denom + 1; // denom is negative numbrt
                sign_d = 1'b1;
            end

        t_q = t_numer / t_denom; // get quotient
        t_r = t_numer % t_denom; // get remainder
        sign_q = sign_n ^ sign_d;
        sign_r = (t_r != {lpm_widthd{1'b0}}) ? sign_n : 1'b0;

        // Pipeline the result
        tmp_quotient = (sign_q == 1'b1) ? (~t_q + 1) : t_q;
        tmp_remain   = (sign_r == 1'b1) ? (~t_r + 1) : t_r;

        // Recalculate the quotient and remainder if remainder is negative number
        // and LPM_REMAINDERPOSITIVE=TRUE.
        if ((sign_r) && (lpm_remainderpositive == "TRUE"))
        begin
            tmp_quotient = tmp_quotient + ((sign_d == 1'b1) ? 1 : -1 );
            tmp_remain = tmp_remain + t_denom;
        end
    end

    always @(posedge i_clock or posedge i_aclr)
    begin
        if (i_aclr)
        begin
            for (i = 0; i <= (lpm_pipeline+1); i = i + 1)
            begin
                quotient_pipe[i] <= {lpm_widthn{1'b0}};
                remain_pipe[i] <= {lpm_widthd{1'b0}};
            end
            pipe_ptr <= 0;
        end
        else if (i_clken)
        begin
            quotient_pipe[pipe_ptr] <= tmp_quotient;
            remain_pipe[pipe_ptr] <= tmp_remain;

            if (lpm_pipeline > 1)
                pipe_ptr <= (pipe_ptr + 1) % lpm_pipeline;
        end
    end

// CONTINOUS ASSIGNMENT
    assign quotient = (lpm_pipeline > 0) ? quotient_pipe[pipe_ptr] : tmp_quotient;
    assign remain = (lpm_pipeline > 0) ? remain_pipe[pipe_ptr] : tmp_remain;

endmodule // lpm_divide
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_abs
//
// Description     :  Parameterized absolute value megafunction. This megafunction
//                    requires the input data to be signed number.
//
// Limitation      :  n/a
//
// Results expected:  Return absolute value of data and the overflow status
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_abs (
    data,     // Signed number (Required)
    result,   // Absolute value of data[].
    overflow  // High if data = -2 ^ (LPM_WIDTH-1).
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1; // Width of the data[] and result[] ports.(Required)
    parameter lpm_type = "lpm_abs";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;
    output overflow;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_width-1:0] result_tmp;
    reg overflow;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data)
    begin
        result_tmp = (data[lpm_width-1] == 1) ? (~data) + 1 : data;
        overflow = (data[lpm_width-1] == 1) ? (result_tmp == (1<<(lpm_width-1))) : 0;
    end

// CONTINOUS ASSIGNMENT
    assign result = result_tmp;

endmodule // lpm_abs

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_counter
//
// Description     :  Parameterized counter megafunction. The lpm_counter
//                    megafunction is a binary counter that features an up,
//                    down, or up/down counter with optional synchronous or
//                    asynchronous clear, set, and load ports.
//
// Limitation      :  n/a
//
// Results expected:  Data output from the counter and carry-out of the MSB.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_counter (
    clock,  // Positive-edge-triggered clock. (Required)
    clk_en, // Clock enable input. Enables all synchronous activities.
    cnt_en, // Count enable input. Disables the count when low (0) without
            // affecting sload, sset, or sclr.
    updown, // Controls the direction of the count. High (1) = count up.
            //                                      Low (0) = count down.
    aclr,   // Asynchronous clear input.
    aset,   // Asynchronous set input.
    aload,  // Asynchronous load input. Asynchronously loads the counter with
            // the value on the data input.
    sclr,   // Synchronous clear input. Clears the counter on the next active
            // clock edge.
    sset,   // Synchronous set input. Sets the counter on the next active clock edge.
    sload,  // Synchronous load input. Loads the counter with data[] on the next
            // active clock edge.
    data,   // Parallel data input to the counter.
    cin,    // Carry-in to the low-order bit.
    q,      // Data output from the counter.
    cout,   // Carry-out of the MSB.
    eq      // Counter decode output. Active high when the counter reaches the specified
            // count value.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;    //The number of bits in the count, or the width of the q[]
                                // and data[] ports, if they are used. (Required)
    parameter lpm_direction = "UNUSED"; // Direction of the count.
    parameter lpm_modulus = 0;          // The maximum count, plus one.
    parameter lpm_avalue = "UNUSED";    // Constant value that is loaded when aset is high.
    parameter lpm_svalue = "UNUSED";    // Constant value that is loaded on the rising edge
                                        // of clock when sset is high.
    parameter lpm_pvalue = "UNUSED";
    parameter lpm_port_updown = "PORT_CONNECTIVITY";
    parameter lpm_type = "lpm_counter";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  clock;
    input  clk_en;
    input  cnt_en;
    input  updown;
    input  aclr;
    input  aset;
    input  aload;
    input  sclr;
    input  sset;
    input  sload;
    input  [lpm_width-1:0] data;
    input  cin;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;
    output cout;
    output [15:0] eq;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg  [lpm_width-1:0] tmp_count;
    reg  [lpm_width-1:0] adata;

    reg  use_adata;
    reg  tmp_updown;
    reg  [lpm_width:0] tmp_modulus;
    reg  [lpm_width:0] max_modulus;
    reg  [lpm_width-1:0] svalue;
    reg  [lpm_width-1:0] avalue;
    reg  [lpm_width-1:0] pvalue;

// INTERNAL WIRE DECLARATION
    wire w_updown;
    wire [lpm_width-1:0] final_count;

// LOCAL INTEGER DECLARATION
    integer i;

// INTERNAL TRI DECLARATION

    tri1 clk_en;
    tri1 cnt_en;
    tri0 aclr;
    tri0 aset;
    tri0 aload;
    tri0 sclr;
    tri0 sset;
    tri0 sload;
    tri1 cin;
    tri1 updown_z;

    wire i_clk_en;
    wire i_cnt_en;
    wire i_aclr;
    wire i_aset;
    wire i_aload;
    wire i_sclr;
    wire i_sset;
    wire i_sload;
    wire i_cin;
    wire i_updown;
    buf (i_clk_en, clk_en);
    buf (i_cnt_en, cnt_en);
    buf (i_aclr, aclr);
    buf (i_aset, aset);
    buf (i_aload, aload);
    buf (i_sclr, sclr);
    buf (i_sset, sset);
    buf (i_sload, sload);
    buf (i_cin, cin);
    buf (i_updown, updown_z);

// TASK DECLARATION
    task string_to_reg;
    input  [8*40:1] string_value;
    output [lpm_width-1:0] value;

    reg [8*40:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    reg [lpm_width-1:0] ivalue;

    integer m;

    begin
        ivalue = {lpm_width{1'b0}};
        reg_s = string_value;
        for (m=1; m<=40; m=m+1)
        begin
            tmp = reg_s[320:313];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            ivalue = ivalue * 10 + digit;
        end
        value = ivalue;
    end
    endtask

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        max_modulus = 1 << lpm_width;

        // check if lpm_width < 0
        if (lpm_width <= 0)
        begin
            $display("Error!  LPM_WIDTH must be greater than 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        // check if lpm_modulus < 0
        if (lpm_modulus < 0)
        begin
            $display("Error!  LPM_MODULUS must be greater or equal to 0.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        // check if lpm_modulus > 1<<lpm_width
        if (lpm_modulus > max_modulus)
        begin
            $display("Warning!  LPM_MODULUS should be within 1 to 2^LPM_WIDTH. Assuming no modulus input.\n");
            $display ("Time: %0t  Instance: %m", $time);
        end
        // check if lpm_direction valid
        if ((lpm_direction != "UNUSED") && (lpm_direction != "DEFAULT") &&
            (lpm_direction != "UP") && (lpm_direction != "DOWN"))
        begin
            $display("Error!  LPM_DIRECTION must be \"UP\" or \"DOWN\" if used.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_avalue == "UNUSED")
            avalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_avalue, avalue);

        if (lpm_svalue == "UNUSED")
            svalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_svalue, svalue);

        if (lpm_pvalue == "UNUSED")
            pvalue =  {lpm_width{1'b0}};
        else
            string_to_reg(lpm_pvalue, pvalue);

        tmp_modulus = ((lpm_modulus == 0) || (lpm_modulus > max_modulus))
                        ? max_modulus : lpm_modulus;
        tmp_count = pvalue;
        use_adata = 1'b0;
    end

    // NCSIM will only assigns 1'bZ to unconnected port at time 0fs + 1
    // verilator lint_off STMTDLY
    initial #0
    // verilator lint_on STMTDLY
    begin
        // // check if lpm_direction valid
        if ((lpm_direction != "UNUSED") && (lpm_direction != "DEFAULT") && (updown !== 1'bz) &&
            (lpm_port_updown == "PORT_CONNECTIVITY"))
        begin
            $display("Error!  LPM_DIRECTION and UPDOWN cannot be used at the same time.\n");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(posedge i_aclr or posedge i_aset or posedge i_aload or posedge clock)
    begin
        if (i_aclr || i_aset || i_aload)
            use_adata <= 1'b1;
        else if ($time > 0)
        begin
            if (i_clk_en)
            begin
                use_adata <= 1'b0;

                if (i_sclr)
                    tmp_count <= 0;
                else if (i_sset)
                    tmp_count <= svalue;
                else if (i_sload)
                    tmp_count <= data;
                else if (i_cnt_en && i_cin)
                begin
                    if (w_updown)
                        tmp_count <= (final_count == tmp_modulus-1) ? 0
                                                    : final_count+1;
                    else
                        tmp_count <= (final_count == 0) ? tmp_modulus-1
                                                    : final_count-1;
                end
                else
                    tmp_count <= final_count;
            end
        end
    end

    always @(i_aclr or i_aset or i_aload or data or avalue)
    begin
        if (i_aclr)
        begin
            adata <= 0;
        end
        else if (i_aset)
        begin
            adata <= avalue;
        end
        else if (i_aload)
            adata <= data;
    end

// CONTINOUS ASSIGNMENT
    assign q = final_count;
    assign final_count = (use_adata == 1'b1) ? adata : tmp_count;
    assign cout = (i_cin && (((w_updown==0) && (final_count==0)) ||
                            ((w_updown==1) && ((final_count==tmp_modulus-1) ||
                                                (final_count=={lpm_width{1'b1}}))) ))
                    ? 1'b1 : 1'b0;
    assign updown_z = updown;
    assign w_updown =   (lpm_port_updown == "PORT_USED") ? i_updown :
                        (lpm_port_updown == "PORT_UNUSED") ? ((lpm_direction == "DOWN") ? 1'b0 : 1'b1) :
                        ((((lpm_direction == "UNUSED") || (lpm_direction == "DEFAULT")) && (i_updown == 1)) ||
                        (lpm_direction == "UP"))
                        ? 1'b1 : 1'b0;
    assign eq = {16{1'b0}};

endmodule // lpm_counter
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_latch
//
// Description     :  Parameterized latch megafunction.
//
// Limitation      :  n/a
//
// Results expected:  Data output from the latch.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_latch (
    data,  // Data input to the latch.
    gate,  // Latch enable input. High = flow-through, low = latch. (Required)
    aclr,  // Asynchronous clear input.
    aset,  // Asynchronous set input.
    aconst,
    q      // Data output from the latch.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;         // Width of the data[] and q[] ports. (Required)
    parameter lpm_avalue = "UNUSED"; // Constant value that is loaded when aset is high.
    parameter lpm_pvalue = "UNUSED";
    parameter lpm_type = "lpm_latch";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  gate;
    input  aclr;
    input  aset;
    input  aconst;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_width-1:0] q;
    reg [lpm_width-1:0] avalue;
    reg [lpm_width-1:0] pvalue;


// INTERNAL TRI DECLARATION
    tri0 [lpm_width-1:0] data;
    tri0 aclr;
    tri0 aset;
    tri0 aconst;

    wire i_aclr;
    wire i_aset;
    buf (i_aclr, aclr);
    buf (i_aset, aset);

// TASK DECLARATION
    task string_to_reg;
    input  [8*40:1] string_value;
    output [lpm_width-1:0] value;

    reg [8*40:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    reg [lpm_width-1:0] ivalue;

    integer m;

    begin
        ivalue = {lpm_width{1'b0}};
        reg_s = string_value;
        for (m=1; m<=40; m=m+1)
        begin
            tmp = reg_s[320:313];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            ivalue = ivalue * 10 + digit;
        end
        value = ivalue;
    end
    endtask

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_pvalue != "UNUSED")
        begin
            string_to_reg(lpm_pvalue, pvalue);
            q = pvalue;
        end

        if (lpm_avalue == "UNUSED")
            avalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_avalue, avalue);
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data or gate or i_aclr or i_aset or avalue)
    begin
        if (i_aclr)
            q <= {lpm_width{1'b0}};
        else if (i_aset)
            q <= avalue;
        else if (gate)
            q <= data;
    end

endmodule // lpm_latch

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_ff
//
// Description     :  Parameterized flipflop megafunction. The lpm_ff function
//                    contains features that are not available in the DFF, DFFE,
//                    DFFEA, TFF, and TFFE primitives, such as synchronous or
//                    asynchronous set, clear, and load inputs.

//
// Limitation      :  n/a
//
// Results expected:  Data output from D or T flipflops.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_ff (
    data,   // T-type flipflop: Toggle enable
            // D-type flipflop: Data input

    clock,  // Positive-edge-triggered clock. (Required)
    enable, // Clock enable input.
    aclr,   // Asynchronous clear input.
    aset,   // Asynchronous set input.

    aload,  // Asynchronous load input. Asynchronously loads the flipflop with
            // the value on the data input.

    sclr,   // Synchronous clear input.
    sset,   // Synchronous set input.

    sload,  // Synchronous load input. Loads the flipflop with the value on the
            // data input on the next active clock edge.

    q       // Data output from D or T flipflops. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width  = 1; // Width of the data[] and q[] ports. (Required)
    parameter lpm_avalue = "UNUSED";    // Constant value that is loaded when aset is high.
    parameter lpm_svalue = "UNUSED";    // Constant value that is loaded on the rising edge
                                        // of clock when sset is high.
    parameter lpm_pvalue = "UNUSED";
    parameter lpm_fftype = "DFF";       // Type of flipflop
    parameter lpm_type = "lpm_ff";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  clock;
    input  enable;
    input  aclr;
    input  aset;
    input  aload;
    input  sclr;
    input  sset;
    input  sload ;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg  [lpm_width-1:0] tmp_q;
    reg  [lpm_width-1:0] adata;
    reg  use_adata;
    reg  [lpm_width-1:0] svalue;
    reg  [lpm_width-1:0] avalue;
    reg  [lpm_width-1:0] pvalue;

// INTERNAL WIRE DECLARATION
    wire [lpm_width-1:0] final_q;

// LOCAL INTEGER DECLARATION
    integer i;

// INTERNAL TRI DECLARATION
    tri1  [lpm_width-1:0] data;
    tri1 enable;
    tri0 sload;
    tri0 sclr;
    tri0 sset;
    tri0 aload;
    tri0 aclr;
    tri0 aset;

    wire i_enable;
    wire i_sload;
    wire i_sclr;
    wire i_sset;
    wire i_aload;
    wire i_aclr;
    wire i_aset;
    buf (i_enable, enable);
    buf (i_sload, sload);
    buf (i_sclr, sclr);
    buf (i_sset, sset);
    buf (i_aload, aload);
    buf (i_aclr, aclr);
    buf (i_aset, aset);

// TASK DECLARATION
    task string_to_reg;
    input  [8*40:1] string_value;
    output [lpm_width-1:0] value;

    reg [8*40:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    reg [lpm_width-1:0] ivalue;

    integer m;

    begin
        ivalue = {lpm_width{1'b0}};
        reg_s = string_value;
        for (m=1; m<=40; m=m+1)
        begin
            tmp = reg_s[320:313];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            ivalue = ivalue * 10 + digit;
        end
        value = ivalue;
    end
    endtask

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_fftype != "DFF") &&
            (lpm_fftype != "TFF") &&
            (lpm_fftype != "UNUSED"))          // non-LPM 220 standard
        begin
            $display("Error!  LPM_FFTYPE value must be \"DFF\" or \"TFF\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_avalue == "UNUSED")
            avalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_avalue, avalue);

        if (lpm_svalue == "UNUSED")
            svalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_svalue, svalue);

        if (lpm_pvalue == "UNUSED")
            pvalue =  {lpm_width{1'b0}};
        else
            string_to_reg(lpm_pvalue, pvalue);

        tmp_q = pvalue;
        use_adata = 1'b0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(posedge i_aclr or posedge i_aset or posedge i_aload or posedge clock)
    begin // Asynchronous process
        if (i_aclr || i_aset || i_aload)
            use_adata <= 1'b1;
        else if ($time > 0)
        begin // Synchronous process
            if (i_enable)
            begin
                use_adata <= 1'b0;

                if (i_sclr)
                    tmp_q <= 0;
                else if (i_sset)
                    tmp_q <= svalue;
                else if (i_sload)  // Load data
                    tmp_q <= data;
                else
                begin
                    if (lpm_fftype == "TFF") // toggle
                    begin
                        for (i = 0; i < lpm_width; i=i+1)
                            if (data[i] == 1'b1)
                                tmp_q[i] <= ~final_q[i];
                            else
                                tmp_q[i] <= final_q[i];
                    end
                    else    // DFF, load data
                        tmp_q <= data;
                end
            end
        end
    end

    always @(i_aclr or i_aset or i_aload or data or avalue or pvalue)
    begin
        if (i_aclr === 1'b1)
            adata <= {lpm_width{1'b0}};
        else if (i_aclr === 1'bx)
            adata <= {lpm_width{1'bx}};
        else if (i_aset)
            adata <= avalue;
        else if (i_aload)
            adata <= data;
        else if ((i_aclr === 1'b0) && ($time == 0))
            adata <= pvalue;
    end

// CONTINOUS ASSIGNMENT
    assign q = final_q;
    assign final_q = (use_adata == 1'b1) ? adata : tmp_q;

endmodule // lpm_ff
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_shiftreg
//
// Description     :  Parameterized shift register megafunction.
//
// Limitation      :  n/a
//
// Results expected:  Data output from the shift register and the Serial shift data output.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_shiftreg (
    data,       // Data input to the shift register.
    clock,      // Positive-edge-triggered clock. (Required)
    enable,     // Clock enable input
    shiftin,    // Serial shift data input.
    load,       // Synchronous parallel load. High (1): load operation;
                //                            low (0): shift operation.
    aclr,       // Asynchronous clear input.
    aset,       // Asynchronous set input.
    sclr,       // Synchronous clear input.
    sset,       // Synchronous set input.
    q,          // Data output from the shift register.
    shiftout    // Serial shift data output.
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width  = 1;  // Width of the data[] and q ports. (Required)
    parameter lpm_direction = "LEFT";   // Values are "LEFT", "RIGHT", and "UNUSED".
    parameter lpm_avalue = "UNUSED";    // Constant value that is loaded when aset is high.
    parameter lpm_svalue = "UNUSED";    // Constant value that is loaded on the rising edge
                                        // of clock when sset is high.
    parameter lpm_pvalue = "UNUSED";
    parameter lpm_type = "lpm_shiftreg";
    parameter lpm_hint  = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  clock;
    input  enable;
    input  shiftin;
    input  load;
    input  aclr;
    input  aset;
    input  sclr;
    input  sset;


// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;
    output shiftout;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg  [lpm_width-1:0] tmp_q;
    reg  abit;
    reg  [lpm_width-1:0] svalue;
    reg  [lpm_width-1:0] avalue;
    reg  [lpm_width-1:0] pvalue;

// LOCAL INTEGER DECLARATION
    integer i;

// INTERNAL WIRE DECLARATION
    wire tmp_shiftout;

// INTERNAL TRI DECLARATION
    tri1 enable;
    tri1 shiftin;
    tri0 load;
    tri0 aclr;
    tri0 aset;
    tri0 sclr;
    tri0 sset;

    wire i_enable;
    wire i_shiftin;
    wire i_load;
    wire i_aclr;
    wire i_aset;
    wire i_sclr;
    wire i_sset;
    buf (i_enable, enable);
    buf (i_shiftin, shiftin);
    buf (i_load, load);
    buf (i_aclr, aclr);
    buf (i_aset, aset);
    buf (i_sclr, sclr);
    buf (i_sset, sset);

// TASK DECLARATION
    task string_to_reg;
    input  [8*40:1] string_value;
    output [lpm_width-1:0] value;

    reg [8*40:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    reg [lpm_width-1:0] ivalue;

    integer m;

    begin
        ivalue = {lpm_width{1'b0}};
        reg_s = string_value;
        for (m=1; m<=40; m=m+1)
        begin
            tmp = reg_s[320:313];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            ivalue = ivalue * 10 + digit;
        end
        value = ivalue;
    end
    endtask

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0 (ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_direction != "LEFT") &&
            (lpm_direction != "RIGHT") &&
            (lpm_direction != "UNUSED"))          // non-LPM 220 standard
        begin
            $display("Error!  LPM_DIRECTION value must be \"LEFT\" or \"RIGHT\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_avalue == "UNUSED")
            avalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_avalue, avalue);

        if (lpm_svalue == "UNUSED")
            svalue =  {lpm_width{1'b1}};
        else
            string_to_reg(lpm_svalue, svalue);

        if (lpm_pvalue == "UNUSED")
            pvalue =  {lpm_width{1'b0}};
        else
            string_to_reg(lpm_pvalue, pvalue);

        tmp_q = pvalue;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(i_aclr or i_aset or avalue)
    begin
        if (i_aclr)
            tmp_q <= {lpm_width{1'b0}};
        else if (i_aset)
            tmp_q <= avalue;
    end

    always @(posedge clock)
    begin
        if (i_aclr)
            tmp_q <= (i_aset) ? {lpm_width{1'bx}} : {lpm_width{1'b0}};
        else if (i_aset)
            tmp_q <= avalue;
        else
        begin
            if (i_enable)
            begin
                if (i_sclr)
                    tmp_q <= {lpm_width{1'b0}};
                else if (i_sset)
                    tmp_q <= svalue;
                else if (i_load)
                    tmp_q <= data;
                else if (!i_load)
                begin
                    if ((lpm_direction == "LEFT") || (lpm_direction == "UNUSED"))
                        {abit,tmp_q} <= {tmp_q,i_shiftin};
                    else if (lpm_direction == "RIGHT")
                        {tmp_q,abit} <= {i_shiftin,tmp_q};
                end
            end
        end
    end

// CONTINOUS ASSIGNMENT
    assign tmp_shiftout = (lpm_direction == "RIGHT") ? tmp_q[0]
                                                    : tmp_q[lpm_width-1];
    assign q = tmp_q;
    assign shiftout = tmp_shiftout;

endmodule // lpm_shiftreg
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_ram_dq
//
// Description     :  Parameterized RAM with separate input and output ports megafunction.
//                    lpm_ram_dq implement asynchronous memory or memory with synchronous
//                    inputs and/or outputs.
//
// Limitation      :  n/a
//
// Results expected:  Data output from the memory.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_ram_dq (
    data,      // Data input to the memory. (Required)
    address,   // Address input to the memory. (Required)
    inclock,   // Synchronizes memory loading.
    outclock,  // Synchronizes q outputs from memory.
    we,        // Write enable input. Enables write operations to the memory when high. (Required)
    q          // Data output from the memory. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;  // Width of data[] and q[] ports. (Required)
    parameter lpm_widthad = 1; // Width of the address port. (Required)
    parameter lpm_numwords = 1 << lpm_widthad; // Number of words stored in memory.
    parameter lpm_indata = "REGISTERED";  // Controls whether the data port is registered.
    parameter lpm_address_control = "REGISTERED"; // Controls whether the address and we ports are registered.
    parameter lpm_outdata = "REGISTERED"; // Controls whether the q ports are registered.
    parameter lpm_file = "UNUSED"; // Name of the file containing RAM initialization data.
    parameter use_eab = "ON"; // Specified whether to use the EAB or not.
    parameter intended_device_family = "Stratix";
    parameter lpm_type = "lpm_ram_dq";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  [lpm_widthad-1:0] address;
    input  inclock;
    input  outclock;
    input  we;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;


// INTERNAL REGISTER/SIGNAL DECLARATION
    reg  [lpm_width-1:0] mem_data [lpm_numwords-1:0];
    reg  [lpm_width-1:0] tmp_q;
    reg  [lpm_width-1:0] pdata;
    reg  [lpm_width-1:0] in_data;
    reg  [lpm_widthad-1:0] paddress;
    reg  pwe;
    reg  [lpm_width-1:0]  ZEROS, ONES, UNKNOWN;
`ifdef VERILATOR
    reg  [`LPM_MAX_NAME_SZ*8:1] ram_initf;
`else
    reg  [8*256:1] ram_initf;
`endif

// LOCAL INTEGER DECLARATION
    integer i;

// INTERNAL TRI DECLARATION
    tri0 inclock;
    tri0 outclock;

    wire i_inclock;
    wire i_outclock;
    buf (i_inclock, inclock);
    buf (i_outclock, outclock);

// COMPONENT INSTANTIATIONS
    LPM_DEVICE_FAMILIES dev ();
    LPM_MEMORY_INITIALIZATION mem ();

// FUNCTON DECLARATION
    // Check the validity of the address.
    function ValidAddress;
        input [lpm_widthad-1:0] paddress;

        begin
            ValidAddress = 1'b0;
            if (^paddress === {lpm_widthad{1'bx}})
            begin
                $display("%t:Error!  Invalid address.\n", $time);
                $display("Time: %0t  Instance: %m", $time);
            end
            else if (paddress >= lpm_numwords)
            begin
                $display("%t:Error!  Address out of bound on RAM.\n", $time);
                $display("Time: %0t  Instance: %m", $time);
            end
            else
                ValidAddress = 1'b1;
        end
    endfunction

// INITIAL CONSTRUCT BLOCK
    initial
    begin

        // Initialize the internal data register.
        pdata = {lpm_width{1'b0}};
        paddress = {lpm_widthad{1'b0}};
        pwe = 1'b0;

        if (lpm_width <= 0)
        begin
            $display("Error!  LPM_WIDTH parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_widthad <= 0)
        begin
            $display("Error!  LPM_WIDTHAD parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        // check for number of words out of bound
        if ((lpm_numwords > (1 << lpm_widthad)) ||
            (lpm_numwords <= (1 << (lpm_widthad-1))))
        begin
            $display("Error!  The ceiling of log2(LPM_NUMWORDS) must equal to LPM_WIDTHAD.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_address_control != "REGISTERED") && (lpm_address_control != "UNREGISTERED"))
        begin
            $display("Error!  LPM_ADDRESS_CONTROL must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_indata != "REGISTERED") && (lpm_indata != "UNREGISTERED"))
        begin
            $display("Error!  LPM_INDATA must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_outdata != "REGISTERED") && (lpm_outdata != "UNREGISTERED"))
        begin
            $display("Error!  LPM_OUTDATA must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (dev.IS_VALID_FAMILY(intended_device_family) == 0)
        begin
            $display ("Error! Unknown INTENDED_DEVICE_FAMILY=%s.", intended_device_family);
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        for (i=0; i < lpm_width; i=i+1)
        begin
            ZEROS[i] = 1'b0;
            ONES[i] = 1'b1;
            UNKNOWN[i] = 1'bX;
        end

        for (i = 0; i < lpm_numwords; i=i+1)
            mem_data[i] = {lpm_width{1'b0}};

        // load data to the RAM
        if (lpm_file != "UNUSED")
        begin
            mem.convert_to_ver_file(lpm_file, lpm_width, ram_initf);
            $readmemh(ram_initf, mem_data);
        end

        tmp_q = ZEROS;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(posedge i_inclock)
    begin
        if (lpm_address_control == "REGISTERED")
        begin
            if ((we) && (use_eab != "ON") &&
                (lpm_hint != "USE_EAB=ON"))
            begin
                if (lpm_indata == "REGISTERED")
                    mem_data[address] <= data;
                else
                    mem_data[address] <= pdata;
            end
            paddress <= address;
            pwe <= we;
        end
        if (lpm_indata == "REGISTERED")
            pdata <= data;
    end

    always @(data)
    begin
        if (lpm_indata == "UNREGISTERED")
            pdata <= data;
    end

    always @(address)
    begin
        if (lpm_address_control == "UNREGISTERED")
            paddress <= address;
    end

    always @(we)
    begin
        if (lpm_address_control == "UNREGISTERED")
            pwe <= we;
    end

    always @(pdata or paddress or pwe)
    begin :UNREGISTERED_INCLOCK
        if (ValidAddress(paddress))
        begin
            if ((lpm_address_control == "UNREGISTERED") && (pwe))
                mem_data[paddress] <= pdata;
            end
        else
        begin
            if (lpm_outdata == "UNREGISTERED")
                tmp_q <= {lpm_width{1'bx}};
        end
    end

    always @(posedge i_outclock)
    begin
        if (lpm_outdata == "REGISTERED")
        begin
            if (ValidAddress(paddress))
                tmp_q <= mem_data[paddress];
            else
                tmp_q <= {lpm_width{1'bx}};
        end
    end

    always @(i_inclock or pwe or paddress or pdata)
    begin
        if ((lpm_address_control == "REGISTERED") && (pwe))
            if ((use_eab == "ON") || (lpm_hint == "USE_EAB=ON"))
            begin
                if (i_inclock == 1'b0)
                    mem_data[paddress] = pdata;
            end
    end

// CONTINOUS ASSIGNMENT
    assign q = (lpm_outdata == "UNREGISTERED") ? mem_data[paddress] : tmp_q;

endmodule // lpm_ram_dq
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_ram_dp
//
// Description     :  Parameterized dual-port RAM megafunction.
//
// Limitation      :  n/a
//
// Results expected:  Data output from the memory.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_ram_dp (
    data,      // Data input to the memory. (Required)
    rdaddress, // Read address input to the memory. (Required)
    wraddress, // Write address input to the memory. (Required)
    rdclock,   // Positive-edge-triggered clock for read operation.
    rdclken,   // Clock enable for rdclock.
    wrclock,   // Positive-edge-triggered clock for write operation.
    wrclken,   // Clock enable for wrclock.
    rden,      // Read enable input. Disables reading when low (0).
    wren,      // Write enable input. (Required)
    q          // Data output from the memory. (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;   // Width of the data[] and q[] ports. (Required)
    parameter lpm_widthad = 1; // Width of the rdaddress[] and wraddress[] ports. (Required)
    parameter lpm_numwords = 1 << lpm_widthad; // Number of words stored in memory.
    parameter lpm_indata = "REGISTERED"; // Determines the clock used by the data port.
    parameter lpm_rdaddress_control  = "REGISTERED"; // Determines the clock used by the rdaddress and rden ports.
    parameter lpm_wraddress_control  = "REGISTERED"; // Determines the clock used by the wraddress and wren ports.
    parameter lpm_outdata = "REGISTERED"; // Determines the clock used by the q[] pxort.
    parameter lpm_file = "UNUSED"; // Name of the file containing RAM initialization data.
    parameter use_eab = "ON"; // Specified whether to use the EAB or not.
    parameter rden_used = "TRUE"; // Specified whether to use the rden port or not.
    parameter intended_device_family = "Stratix";
    parameter lpm_type = "lpm_ram_dp";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  [lpm_widthad-1:0] rdaddress;
    input  [lpm_widthad-1:0] wraddress;
    input  rdclock;
    input  rdclken;
    input  wrclock;
    input  wrclken;
    input  rden;
    input  wren;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg [lpm_width-1:0] mem_data [(1<<lpm_widthad)-1:0];
    reg [lpm_width-1:0] i_data_reg, i_data_tmp, i_q_reg, i_q_tmp;
    reg [lpm_widthad-1:0] i_wraddress_reg, i_wraddress_tmp;
    reg [lpm_widthad-1:0] i_rdaddress_reg, i_rdaddress_tmp;
    reg i_wren_reg, i_wren_tmp, i_rden_reg, i_rden_tmp;
`ifdef VERILATOR
    reg  [`LPM_MAX_NAME_SZ*8:1] ram_initf;
`else
    reg  [8*256:1] ram_initf;
`endif

// LOCAL INTEGER DECLARATION
    integer i, i_numwords;

// INTERNAL TRI DECLARATION
    tri0 wrclock;
    tri1 wrclken;
    tri0 rdclock;
    tri1 rdclken;
    tri0 wren;
    tri1 rden;

    wire i_inclock;
    wire i_inclocken;
    wire i_outclock;
    wire i_outclocken;
    wire i_wren;
    wire i_rden;

    buf (i_inclock, wrclock);
    buf (i_inclocken, wrclken);
    buf (i_outclock, rdclock);
    buf (i_outclocken, rdclken);
    buf (i_wren, wren);
    buf (i_rden, rden);

// COMPONENT INSTANTIATIONS
    LPM_DEVICE_FAMILIES dev ();
    LPM_MEMORY_INITIALIZATION mem ();

// FUNCTON DECLARATION
    function ValidAddress;
        input [lpm_widthad-1:0] paddress;

        begin
            ValidAddress = 1'b0;
            if (^paddress === {lpm_widthad{1'bx}})
            begin
                $display("%t:Error!  Invalid address.\n", $time);
                $display("Time: %0t  Instance: %m", $time);
            end
            else if (paddress >= lpm_numwords)
            begin
                $display("%t:Error!  Address out of bound on RAM.\n", $time);
                $display("Time: %0t  Instance: %m", $time);
            end
            else
                ValidAddress = 1'b1;
        end
    endfunction

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        // Check for invalid parameters
        if (lpm_width < 1)
        begin
            $display("Error! lpm_width parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (lpm_widthad < 1)
        begin
            $display("Error! lpm_widthad parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if ((lpm_indata != "REGISTERED") && (lpm_indata != "UNREGISTERED"))
        begin
            $display("Error! lpm_indata must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if ((lpm_outdata != "REGISTERED") && (lpm_outdata != "UNREGISTERED"))
        begin
            $display("Error! lpm_outdata must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if ((lpm_wraddress_control != "REGISTERED") && (lpm_wraddress_control != "UNREGISTERED"))
        begin
            $display("Error! lpm_wraddress_control must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
        end
        if ((lpm_rdaddress_control != "REGISTERED") && (lpm_rdaddress_control != "UNREGISTERED"))
        begin
            $display("Error! lpm_rdaddress_control must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (dev.IS_VALID_FAMILY(intended_device_family) == 0)
        begin
            $display ("Error! Unknown INTENDED_DEVICE_FAMILY=%s.", intended_device_family);
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        // Initialize mem_data
        i_numwords = (lpm_numwords) ? lpm_numwords : (1<<lpm_widthad);

        if (lpm_file == "UNUSED")
            for (i=0; i<i_numwords; i=i+1)
                mem_data[i] = {lpm_width{1'b0}};
        else
        begin
            mem.convert_to_ver_file(lpm_file, lpm_width, ram_initf);
            $readmemh(ram_initf, mem_data);
        end

        // Initialize registers
        i_data_reg = {lpm_width{1'b0}};
        i_wraddress_reg = {lpm_widthad{1'b0}};
        i_rdaddress_reg = {lpm_widthad{1'b0}};
        i_wren_reg = 1'b0;
        if (rden_used == "TRUE")
            i_rden_reg = 1'b0;
        else
            i_rden_reg = 1'b1;

        // Initialize output
        i_q_reg = {lpm_width{1'b0}};
        if ((use_eab == "ON") || (lpm_hint == "USE_EAB=ON"))
        begin
            i_q_tmp = {lpm_width{1'b1}};
        end
        else
            i_q_tmp = {lpm_width{1'b0}};
    end


// ALWAYS CONSTRUCT BLOCK

    always @(posedge i_inclock)
    begin
        if (lpm_indata == "REGISTERED")
            if ((i_inclocken == 1'b1) && ($time > 0))
                i_data_reg <= data;

        if (lpm_wraddress_control == "REGISTERED")
            if ((i_inclocken == 1'b1) && ($time > 0))
            begin
                i_wraddress_reg <= wraddress;
                i_wren_reg <= i_wren;
            end

    end

    always @(posedge i_outclock)
    begin
        if (lpm_outdata == "REGISTERED")
            if ((i_outclocken == 1'b1) && ($time > 0))
            begin
                i_q_reg <= i_q_tmp;
            end

        if (lpm_rdaddress_control == "REGISTERED")
            if ((i_outclocken == 1'b1) && ($time > 0))
            begin
                i_rdaddress_reg <= rdaddress;
                i_rden_reg <= i_rden;
            end
    end


    //=========
    // Memory
    //=========

    always @(i_data_tmp or i_wren_tmp or i_wraddress_tmp or negedge i_inclock)
    begin
        if (i_wren_tmp == 1'b1)
            if (ValidAddress(i_wraddress_tmp))
            begin
                if (((use_eab == "ON") || (lpm_hint == "USE_EAB=ON")) &&
                    (lpm_wraddress_control == "REGISTERED"))
                begin
                    if (i_inclock == 1'b0)
                        mem_data[i_wraddress_tmp] <= i_data_tmp;
                end
                else
                    mem_data[i_wraddress_tmp] <= i_data_tmp;
            end
    end

    always @(i_rden_tmp or i_rdaddress_tmp or mem_data[i_rdaddress_tmp])
    begin
        if (i_rden_tmp == 1'b1)
            i_q_tmp = (ValidAddress(i_rdaddress_tmp))
                        ? mem_data[i_rdaddress_tmp]
                        : {lpm_width{1'bx}};
    end


    //=======
    // Sync
    //=======

    always @(wraddress or i_wraddress_reg)
            i_wraddress_tmp = (lpm_wraddress_control == "REGISTERED")
                        ? i_wraddress_reg
                        : wraddress;
    always @(rdaddress or i_rdaddress_reg)
        i_rdaddress_tmp = (lpm_rdaddress_control == "REGISTERED")
                        ? i_rdaddress_reg
                        : rdaddress;
    always @(i_wren or i_wren_reg)
        i_wren_tmp = (lpm_wraddress_control == "REGISTERED")
                        ? i_wren_reg
                        : i_wren;
    always @(i_rden or i_rden_reg)
        i_rden_tmp = (lpm_rdaddress_control == "REGISTERED")
                        ? i_rden_reg
                        : i_rden;
    always @(data or i_data_reg)
        i_data_tmp = (lpm_indata == "REGISTERED")
                        ? i_data_reg
                        : data;

// CONTINOUS ASSIGNMENT
    assign q = (lpm_outdata == "REGISTERED") ? i_q_reg : i_q_tmp;

endmodule // lpm_ram_dp
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     : lpm_ram_io
//
// Description     : Parameterized RAM with a single I/O port megafunction
//
// Limitation      : This megafunction is provided only for backward
//                   compatibility in Cyclone, Stratix, and Stratix GX designs;
//                   instead, Altera recommends using the altsyncram
//                   megafunction
//
// Results expected: Output of RAM content at bi-directional DIO.
//
//END_MODULE_NAME--------------------------------------------------------------
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_ram_io ( dio, inclock, outclock, we, memenab, outenab, address );

// PARAMETER DECLARATION
    parameter lpm_type = "lpm_ram_io";
    parameter lpm_width = 1;
    parameter lpm_widthad = 1;
    parameter lpm_numwords = 1<< lpm_widthad;
    parameter lpm_indata = "REGISTERED";
    parameter lpm_address_control = "REGISTERED";
    parameter lpm_outdata = "REGISTERED";
    parameter lpm_file = "UNUSED";
    parameter lpm_hint = "UNUSED";
    parameter use_eab = "ON";
    parameter intended_device_family = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_widthad-1:0] address;
    input  inclock, outclock, we;
    input  memenab;
    input  outenab;

// INPUT/OUTPUT PORT DECLARATION
    inout  [lpm_width-1:0] dio;

// INTERNAL REGISTERS DECLARATION
    reg  [lpm_width-1:0] mem_data [lpm_numwords-1:0];
    reg  [lpm_width-1:0] tmp_io;
    reg  [lpm_width-1:0] tmp_q;
    reg  [lpm_width-1:0] pdio;
    reg  [lpm_widthad-1:0] paddress;
    reg  [lpm_widthad-1:0] paddress_tmp;
    reg  pwe;
`ifdef VERILATOR
    reg  [`LPM_MAX_NAME_SZ*8:1] ram_initf;
`else
    reg  [8*256:1] ram_initf;
`endif

// INTERNAL WIRE DECLARATION
    wire [lpm_width-1:0] read_data;
    wire i_inclock;
    wire i_outclock;
    wire i_memenab;
    wire i_outenab;

// LOCAL INTEGER DECLARATION
    integer i;

// INTERNAL TRI DECLARATION
    tri0 inclock;
    tri0 outclock;
    tri1 memenab;
    tri1 outenab;

// INTERNAL BUF DECLARATION
    buf (i_inclock, inclock);
    buf (i_outclock, outclock);
    buf (i_memenab, memenab);
    buf (i_outenab, outenab);


// FUNCTON DECLARATION
    function ValidAddress;
        input [lpm_widthad-1:0] paddress;

        begin
            ValidAddress = 1'b0;
            if (^paddress === {lpm_widthad{1'bx}})
            begin
                $display("%t:Error:  Invalid address.", $time);
                $display("Time: %0t  Instance: %m", $time);
                $finish;
            end
            else if (paddress >= lpm_numwords)
            begin
                $display("%t:Error:  Address out of bound on RAM.", $time);
                $display("Time: %0t  Instance: %m", $time);
                $finish;
            end
            else
                ValidAddress = 1'b1;
        end
    endfunction

// COMPONENT INSTANTIATIONS
    LPM_MEMORY_INITIALIZATION mem ();


// INITIAL CONSTRUCT BLOCK
    initial
    begin

        if (lpm_width <= 0)
        begin
            $display("Error!  LPM_WIDTH parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_widthad <= 0)
        begin
            $display("Error!  LPM_WIDTHAD parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        // check for number of words out of bound
        if ((lpm_numwords > (1 << lpm_widthad))
            ||(lpm_numwords <= (1 << (lpm_widthad-1))))
        begin
            $display("Error!  The ceiling of log2(LPM_NUMWORDS) must equal to LPM_WIDTHAD.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_indata != "REGISTERED") && (lpm_indata != "UNREGISTERED"))
        begin
            $display("Error!  LPM_INDATA must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_address_control != "REGISTERED") && (lpm_address_control != "UNREGISTERED"))
        begin
            $display("Error!  LPM_ADDRESS_CONTROL must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_outdata != "REGISTERED") && (lpm_outdata != "UNREGISTERED"))
        begin
            $display("Error!  LPM_OUTDATA must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        for (i = 0; i < lpm_numwords; i=i+1)
            mem_data[i] = {lpm_width{1'b0}};

        // Initialize input/output
        pwe = 1'b0;
        pdio = {lpm_width{1'b0}};
        paddress = {lpm_widthad{1'b0}};
        paddress_tmp = {lpm_widthad{1'b0}};
        tmp_io = {lpm_width{1'b0}};
        tmp_q = {lpm_width{1'b0}};

        // load data to the RAM
        if (lpm_file != "UNUSED")
        begin
            mem.convert_to_ver_file(lpm_file, lpm_width, ram_initf);
            $readmemh(ram_initf, mem_data);
        end
    end


// ALWAYS CONSTRUCT BLOCK
    always @(dio)
    begin
        if (lpm_indata == "UNREGISTERED")
            pdio <=  dio;
    end

    always @(address)
    begin
        if (lpm_address_control == "UNREGISTERED")
            paddress <=  address;
    end


    always @(we)
    begin
        if (lpm_address_control == "UNREGISTERED")
            pwe <=  we;
    end

    always @(posedge i_inclock)
    begin
        if (lpm_indata == "REGISTERED")
            pdio <=  dio;

        if (lpm_address_control == "REGISTERED")
        begin
            paddress <=  address;
            pwe <=  we;
        end
    end

    always @(pdio or paddress or pwe or i_memenab)
    begin
        if (ValidAddress(paddress))
        begin
            paddress_tmp <= paddress;
            if (lpm_address_control == "UNREGISTERED")
                if (pwe && i_memenab)
                    mem_data[paddress] <= pdio;
        end
        else
        begin
            if (lpm_outdata == "UNREGISTERED")
                tmp_q <= {lpm_width{1'bx}};
        end
    end

    always @(read_data)
    begin
        if (lpm_outdata == "UNREGISTERED")
            tmp_q <= read_data;
    end

    always @(negedge i_inclock or pdio)
    begin
        if (lpm_address_control == "REGISTERED")
            if ((use_eab == "ON") || (lpm_hint == "USE_EAB=ON"))
                if (pwe && i_memenab && (i_inclock == 1'b0))
                    mem_data[paddress] = pdio;
    end

    always @(posedge i_inclock)
    begin
        if (lpm_address_control == "REGISTERED")
            if ((use_eab == "OFF") && pwe && i_memenab)
                mem_data[paddress] <= pdio;
    end

    always @(posedge i_outclock)
    begin
        if (lpm_outdata == "REGISTERED")
            tmp_q <= mem_data[paddress];
    end

    always @(i_memenab or i_outenab or tmp_q)
    begin
        if (i_memenab && i_outenab)
            tmp_io = tmp_q;
        else if ((!i_memenab) || (i_memenab && (!i_outenab)))
            tmp_io = {lpm_width{1'bz}};
    end


// CONTINOUS ASSIGNMENT
    assign dio = tmp_io;
    assign read_data = mem_data[paddress_tmp];

endmodule // lpm_ram_io

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_rom
//
// Description     :  Parameterized ROM megafunction. This megafunction is provided
//                    only for backward compatibility in Cyclone, Stratix, and
//                    Stratix GX designs; instead, Altera recommends using the
//                    altsyncram megafunction.
//
// Limitation      :  This option is available for all Altera devices supported by
//                    the Quartus II software except MAX 3000 and MAX 7000 devices.
//
// Results expected:  Output of memory.
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_rom (
    address,    // Address input to the memory. (Required)
    inclock,    // Clock for input registers.
    outclock,   // Clock for output registers.
    memenab,    // Memory enable input.
    q           // Output of memory.  (Required)
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;    // Width of the q[] port. (Required)
    parameter lpm_widthad = 1;  // Width of the address[] port. (Required)
    parameter lpm_numwords = 0; // Number of words stored in memory.
    parameter lpm_address_control = "REGISTERED"; // Indicates whether the address port is registered.
    parameter lpm_outdata = "REGISTERED"; // Indicates whether the q and eq ports are registered.
    parameter lpm_file = ""; // Name of the memory file containing ROM initialization data
    parameter intended_device_family = "Stratix";
    parameter lpm_type = "lpm_rom";
    parameter lpm_hint = "UNUSED";

// LOCAL_PARAMETERS_BEGIN

    parameter NUM_WORDS = (lpm_numwords == 0) ? (1 << lpm_widthad) : lpm_numwords;

// LOCAL_PARAMETERS_END

// INPUT PORT DECLARATION
    input  [lpm_widthad-1:0] address;
    input  inclock;
    input  outclock;
    input  memenab;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg  [lpm_width-1:0] mem_data [0:NUM_WORDS-1];
    reg  [lpm_widthad-1:0] address_reg;
    reg  [lpm_width-1:0] tmp_q_reg;
`ifdef VERILATOR
    reg  [`LPM_MAX_NAME_SZ*8:1] rom_initf;
`else
    reg  [8*256:1] rom_initf;
`endif

// INTERNAL WIRE DECLARATION
    wire [lpm_widthad-1:0] w_address;
    wire [lpm_width-1:0] w_read_data;
    wire i_inclock;
    wire i_outclock;
    wire i_memenab;

// LOCAL INTEGER DECLARATION
    integer i;

// INTERNAL TRI DECLARATION
    tri0 inclock;
    tri0 outclock;
    tri1 memenab;

    buf (i_inclock, inclock);
    buf (i_outclock, outclock);
    buf (i_memenab, memenab);

// COMPONENT INSTANTIATIONS
    LPM_DEVICE_FAMILIES dev ();
    LPM_MEMORY_INITIALIZATION mem ();

// FUNCTON DECLARATION
    // Check the validity of the address.
    function ValidAddress;
        input [lpm_widthad-1:0] address;
        begin
            ValidAddress = 1'b0;
            if (^address == {lpm_widthad{1'bx}})
            begin
                $display("%d:Error:  Invalid address.", $time);
                $display("Time: %0t  Instance: %m", $time);
                $finish;
            end
            else if (address >= NUM_WORDS)
            begin
                $display("%d:Error:  Address out of bound on ROM.", $time);
                $display("Time: %0t  Instance: %m", $time);
                $finish;
            end
            else
                ValidAddress = 1'b1;
        end
    endfunction

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        // Initialize output
        tmp_q_reg = {lpm_width{1'b0}};
        address_reg = {lpm_widthad{1'b0}};

        if (lpm_width <= 0)
        begin
            $display("Error!  LPM_WIDTH parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (lpm_widthad <= 0)
        begin
            $display("Error!  LPM_WIDTHAD parameter must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        // check for number of words out of bound
        if ((NUM_WORDS > (1 << lpm_widthad)) ||
            (NUM_WORDS <= (1 << (lpm_widthad-1))))
        begin
            $display("Error!  The ceiling of log2(LPM_NUMWORDS) must equal to LPM_WIDTHAD.");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_address_control != "REGISTERED") &&
            (lpm_address_control != "UNREGISTERED"))
        begin
            $display("Error!  LPM_ADDRESS_CONTROL must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if ((lpm_outdata != "REGISTERED") && (lpm_outdata != "UNREGISTERED"))
        begin
            $display("Error!  LPM_OUTDATA must be \"REGISTERED\" or \"UNREGISTERED\".");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        if (dev.IS_VALID_FAMILY(intended_device_family) == 0)
        begin
            $display ("Error! Unknown INTENDED_DEVICE_FAMILY=%s.", intended_device_family);
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
        if (dev.FEATURE_FAMILY_MAX(intended_device_family) == 1)
        begin
            $display ("Error! LPM_ROM megafunction does not support %s devices.", intended_device_family);
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end

        for (i = 0; i < NUM_WORDS; i=i+1)
            mem_data[i] = {lpm_width{1'b0}};

        // load data to the ROM
        if ((lpm_file == "") || (lpm_file == "UNUSED"))
        begin
            $display("Warning:  LPM_ROM must have data file for initialization.\n");
            $display ("Time: %0t  Instance: %m", $time);
        end
        else
        begin
            mem.convert_to_ver_file(lpm_file, lpm_width, rom_initf);
            $readmemh(rom_initf, mem_data);
        end
    end

    always @(posedge i_inclock)
    begin
        if (lpm_address_control == "REGISTERED")
            address_reg <=  address; // address port is registered
    end

    always @(w_address or w_read_data)
    begin
        if (ValidAddress(w_address))
        begin
            if (lpm_outdata == "UNREGISTERED")
                // Load the output register with the contents of the memory location
                // pointed to by address[].
                tmp_q_reg <=  w_read_data;
        end
        else
        begin
            if (lpm_outdata == "UNREGISTERED")
                tmp_q_reg <= {lpm_width{1'bx}};
        end
    end

    always @(posedge i_outclock)
    begin
        if (lpm_outdata == "REGISTERED")
        begin
            if (ValidAddress(w_address))
                tmp_q_reg <=  w_read_data;
            else
                tmp_q_reg <= {lpm_width{1'bx}};
        end
    end

// CONTINOUS ASSIGNMENT
    assign w_address = (lpm_address_control == "REGISTERED") ? address_reg : address;
    assign w_read_data = mem_data[w_address];
    assign q = (i_memenab) ? tmp_q_reg : {lpm_width{1'bz}};

endmodule // lpm_rom
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_fifo
//
// Description     :
//
// Limitation      :
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

`timescale 1 ps / 1 ps

module lpm_fifo (   data,
                    clock,
                    wrreq,
                    rdreq,
                    aclr,
                    sclr,
                    q,
                    usedw,
                    full,
                    empty );

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_widthu = 1;
    parameter lpm_numwords = 2;
    parameter lpm_showahead = "OFF";
    parameter lpm_type = "lpm_fifo";
    parameter lpm_hint = "";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  clock;
    input  wrreq;
    input  rdreq;
    input  aclr;
    input  sclr;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;
    output [lpm_widthu-1:0] usedw;
    output full;
    output empty;

// INTERNAL REGISTERS DECLARATION
    reg [lpm_width-1:0] mem_data [(1<<lpm_widthu):0];
    reg [lpm_width-1:0] tmp_data;
    reg [lpm_widthu-1:0] count_id;
    reg [lpm_widthu-1:0] read_id;
    reg [lpm_widthu-1:0] write_id;
    reg write_flag;
    reg full_flag;
    reg empty_flag;
    reg [lpm_width-1:0] tmp_q;

    reg [8*5:1] overflow_checking;
    reg [8*5:1] underflow_checking;
    reg [8*20:1] allow_rwcycle_when_full;
    reg [8*20:1] intended_device_family;

// INTERNAL WIRE DECLARATION
    wire valid_rreq;
    wire valid_wreq;

// INTERNAL TRI DECLARATION
    tri0 aclr;

// LOCAL INTEGER DECLARATION
    integer i;

// COMPONENT INSTANTIATIONS
    LPM_DEVICE_FAMILIES dev ();
    LPM_HINT_EVALUATION eva();

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display ("Error! LPM_WIDTH must be greater than 0.");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end
        if (lpm_numwords <= 1)
        begin
            $display ("Error! LPM_NUMWORDS must be greater than or equal to 2.");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end
        if ((lpm_widthu !=1) && (lpm_numwords > (1 << lpm_widthu)))
        begin
            $display ("Error! LPM_NUMWORDS must equal to the ceiling of log2(LPM_WIDTHU).");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end
        if (lpm_numwords <= (1 << (lpm_widthu - 1)))
        begin
            $display ("Error! LPM_WIDTHU is too big for the specified LPM_NUMWORDS.");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        overflow_checking = eva.GET_PARAMETER_VALUE(lpm_hint, "OVERFLOW_CHECKING");
        if(overflow_checking == "")
            overflow_checking = "ON";
        else if ((overflow_checking != "ON") && (overflow_checking != "OFF"))
        begin
            $display ("Error! OVERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        underflow_checking = eva.GET_PARAMETER_VALUE(lpm_hint, "UNDERFLOW_CHECKING");
        if(underflow_checking == "")
            underflow_checking = "ON";
        else if ((underflow_checking != "ON") && (underflow_checking != "OFF"))
        begin
            $display ("Error! UNDERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        allow_rwcycle_when_full = eva.GET_PARAMETER_VALUE(lpm_hint, "ALLOW_RWCYCLE_WHEN_FULL");
        if (allow_rwcycle_when_full == "")
            allow_rwcycle_when_full = "OFF";
        else if ((allow_rwcycle_when_full != "ON") && (allow_rwcycle_when_full != "OFF"))
        begin
            $display ("Error! ALLOW_RWCYCLE_WHEN_FULL must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        intended_device_family = eva.GET_PARAMETER_VALUE(lpm_hint, "INTENDED_DEVICE_FAMILY");
        if (intended_device_family == "")
            intended_device_family = "Stratix II";
        else if (dev.IS_VALID_FAMILY(intended_device_family) == 0)
        begin
            $display ("Error! Unknown INTENDED_DEVICE_FAMILY=%s.", intended_device_family);
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end
        for (i = 0; i < (1<<lpm_widthu); i = i + 1)
        begin
            if (dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
                dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family))
                mem_data[i] <= {lpm_width{1'bx}};
            else
                mem_data[i] <= {lpm_width{1'b0}};
        end

        tmp_data <= 0;
        if (dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
            dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family))
            tmp_q <= {lpm_width{1'bx}};
        else
            tmp_q <= {lpm_width{1'b0}};
        write_flag <= 1'b0;
        count_id <= 0;
        read_id <= 0;
        write_id <= 0;
        full_flag <= 1'b0;
        empty_flag <= 1'b1;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(posedge clock or posedge aclr)
    begin
        if (aclr)
        begin
            if (!(dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
                dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family)))
            begin
                if (lpm_showahead == "ON")
                    tmp_q <= mem_data[0];
                else
                    tmp_q <= {lpm_width{1'b0}};
            end

            read_id <= 0;
            count_id <= 0;
            full_flag <= 1'b0;
            empty_flag <= 1'b1;

            if (valid_wreq && (dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
                dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family)))
            begin
                tmp_data <= data;
                write_flag <= 1'b1;
            end
            else
                write_id <= 0;
        end
        else if (sclr)
        begin
            if ((lpm_showahead == "ON") || (dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
                dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family)))
                tmp_q <= mem_data[0];
            else
                tmp_q <= mem_data[read_id];
            read_id <= 0;
            count_id <= 0;
            full_flag <= 1'b0;
            empty_flag <= 1'b1;

            if (valid_wreq)
            begin
                tmp_data <= data;
                write_flag <= 1'b1;
            end
            else
                write_id <= 0;
        end
        else
        begin
            // Both WRITE and READ operations
            if (valid_wreq && valid_rreq)
            begin
                tmp_data <= data;
                write_flag <= 1'b1;
                empty_flag <= 1'b0;
                if (allow_rwcycle_when_full == "OFF")
                begin
                    full_flag <= 1'b0;
                end

                if (read_id >= ((1 << lpm_widthu) - 1))
                begin
                    if (lpm_showahead == "ON")
                        tmp_q <= mem_data[0];
                    else
                        tmp_q <= mem_data[read_id];
                    read_id <= 0;
                end
                else
                begin
                    if (lpm_showahead == "ON")
                        tmp_q <= mem_data[read_id + 1];
                    else
                        tmp_q <= mem_data[read_id];
                    read_id <= read_id + 1;
                end
            end
            // WRITE operation only
            else if (valid_wreq)
            begin
                tmp_data <= data;
                empty_flag <= 1'b0;
                write_flag <= 1'b1;

                if (count_id >= (1 << lpm_widthu) - 1)
                    count_id <= 0;
                else
                    count_id <= count_id + 1;

                if ((count_id == lpm_numwords - 1) && (empty_flag == 1'b0))
                    full_flag <= 1'b1;

                if (lpm_showahead == "ON")
                    tmp_q <= mem_data[read_id];
            end
            // READ operation only
            else if (valid_rreq)
            begin
                full_flag <= 1'b0;

                if (count_id <= 0)
                    count_id <= {lpm_widthu{1'b1}};
                else
                    count_id <= count_id - 1;

                if ((count_id == 1) && (full_flag == 1'b0))
                    empty_flag <= 1'b1;

                if (read_id >= ((1<<lpm_widthu) - 1))
                begin
                    if (lpm_showahead == "ON")
                        tmp_q <= mem_data[0];
                    else
                        tmp_q <= mem_data[read_id];
                    read_id <= 0;
                end
                else
                begin
                    if (lpm_showahead == "ON")
                        tmp_q <= mem_data[read_id + 1];
                    else
                        tmp_q <= mem_data[read_id];
                    read_id <= read_id + 1;
                end
            end // if Both WRITE and READ operations

        end // if aclr
    end // @(posedge clock)

    always @(negedge clock)
    begin
        if (write_flag)
        begin
            write_flag <= 1'b0;
            mem_data[write_id] <= tmp_data;

            if (sclr || aclr || (write_id >= ((1 << lpm_widthu) - 1)))
                write_id <= 0;
            else
                write_id <= write_id + 1;
        end

        if ((lpm_showahead == "ON") && ($time > 0))
            tmp_q <= ((write_flag == 1'b1) && (write_id == read_id)) ?
                        tmp_data : mem_data[read_id];

    end // @(negedge clock)

// CONTINOUS ASSIGNMENT
    assign valid_rreq = (underflow_checking == "OFF") ? rdreq : rdreq && ~empty_flag;
    assign valid_wreq = (overflow_checking == "OFF") ? wrreq :
                        (allow_rwcycle_when_full == "ON") ? wrreq && (!full_flag || rdreq) :
                        wrreq && !full_flag;
    assign q = tmp_q;
    assign full = full_flag;
    assign empty = empty_flag;
    assign usedw = count_id;

endmodule // lpm_fifo
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_fifo_dc_dffpipe
//
// Description     :  Dual Clocks FIFO
//
// Limitation      :
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_fifo_dc_dffpipe (d,
                            clock,
                            aclr,
                            q);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_delay = 1;
    parameter lpm_width = 64;

// INPUT PORT DECLARATION
    input [lpm_width-1:0] d;
    input clock;
    input aclr;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] q;

// INTERNAL REGISTERS DECLARATION
    reg [lpm_width-1:0] dffpipe [lpm_delay:0];
    reg [lpm_width-1:0] q;

// LOCAL INTEGER DECLARATION
    integer delay;
    integer i;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        delay <= lpm_delay - 1;

        for (i = 0; i <= lpm_delay; i = i + 1)
            dffpipe[i] <= 0;
        q <= 0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(posedge aclr or posedge clock)
    begin
        if (aclr)
        begin
            for (i = 0; i <= lpm_delay; i = i + 1)
                dffpipe[i] <= 0;
            q <= 0;
        end
        else if (clock)
        begin
            if ((lpm_delay > 0) && ($time > 0))
            begin
`ifdef VERILATOR
                if (lpm_delay > 0)
`else
                if (delay > 0)
`endif
                begin
`ifdef VERILATOR
                    for (i = lpm_delay-1; i > 0; i = i - 1)
`else
                    for (i = delay; i > 0; i = i - 1)
`endif
                        dffpipe[i] <= dffpipe[i - 1];
                    q <= dffpipe[delay - 1];
                end
                else
                    q <= d;

                dffpipe[0] <= d;
            end
        end
    end // @(posedge aclr or posedge clock)

    always @(d)
    begin
        if (lpm_delay == 0)
            q <= d;
    end // @(d)

endmodule // lpm_fifo_dc_dffpipe
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_fifo_dc_fefifo
//
// Description     :  Dual Clock FIFO
//
// Limitation      :
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_fifo_dc_fefifo ( usedw_in,
                            wreq,
                            rreq,
                            clock,
                            aclr,
                            empty,
                            full);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_widthad = 1;
    parameter lpm_numwords = 1;
    parameter underflow_checking = "ON";
    parameter overflow_checking = "ON";
    parameter lpm_mode = "READ";
    parameter lpm_hint = "";

// INPUT PORT DECLARATION
    input [lpm_widthad-1:0] usedw_in;
    input wreq;
    input rreq;
    input clock;
    input aclr;

// OUTPUT PORT DECLARATION
    output empty;
    output full;

// INTERNAL REGISTERS DECLARATION
    reg [1:0] sm_empty;
    reg lrreq;
    reg i_empty;
    reg i_full;
    reg [8*5:1] i_overflow_checking;
    reg [8*5:1] i_underflow_checking;

// LOCAL INTEGER DECLARATION
    integer almostfull;

// COMPONENT INSTANTIATIONS
    LPM_HINT_EVALUATION eva();

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if ((lpm_mode != "READ") && (lpm_mode != "WRITE"))
        begin
            $display ("Error! LPM_MODE must be READ or WRITE.");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        i_overflow_checking = eva.GET_PARAMETER_VALUE(lpm_hint, "OVERFLOW_CHECKING");
        if (i_overflow_checking == "")
        begin
            if ((overflow_checking != "ON") && (overflow_checking != "OFF"))
            begin
                $display ("Error! OVERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
                $display("Time: %0t  Instance: %m", $time);
                $stop;
            end
            else
                i_overflow_checking = overflow_checking;
        end
        else if ((i_overflow_checking != "ON") && (i_overflow_checking != "OFF"))
        begin
            $display ("Error! OVERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        i_underflow_checking = eva.GET_PARAMETER_VALUE(lpm_hint, "UNDERFLOW_CHECKING");
        if(i_underflow_checking == "")
        begin
            if ((underflow_checking != "ON") && (underflow_checking != "OFF"))
            begin
                $display ("Error! UNDERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
                $display("Time: %0t  Instance: %m", $time);
                $stop;
            end
            else
                i_underflow_checking = underflow_checking;
        end
        else if ((i_underflow_checking != "ON") && (i_underflow_checking != "OFF"))
        begin
            $display ("Error! UNDERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        sm_empty <= 2'b00;
        i_empty <= 1'b1;
        i_full <= 1'b0;
        lrreq <= 1'b0;

        if (lpm_numwords >= 3)
            almostfull <= lpm_numwords - 3;
        else
            almostfull <= 0;
    end

// ALWAYS CONSTRUCT BLOCK
    always @(posedge aclr)
    begin
        sm_empty <= 2'b00;
        i_empty <= 1'b1;
        i_full <= 1'b0;
        lrreq <= 1'b0;
    end // @(posedge aclr)

    always @(posedge clock)
    begin
        if (i_underflow_checking == "OFF")
            lrreq <= rreq;
        else
            lrreq <= rreq && ~i_empty;

        if (~aclr && ($time > 0))
        begin
            if (lpm_mode == "READ")
            begin
                // verilator lint_off CASEX
                casex (sm_empty)
                // verilator lint_on CASEX
                    // state_empty
                    2'b00:
                        if (usedw_in != 0)
                            sm_empty <= 2'b01;
                    // state_non_empty
                    // verilator lint_off CMPCONST
                    2'b01:
                        if (rreq && (((usedw_in == 1) && !lrreq) || ((usedw_in == 2) && lrreq)))
                            sm_empty <= 2'b10;
                    // state_emptywait
                    2'b10:
                        if (usedw_in > 1)
                            sm_empty <= 2'b01;
                        else
                            sm_empty <= 2'b00;
                    // verilator lint_on CMPCONST
                    default:
                        begin
                            $display ("Error! Invalid sm_empty state in read mode.");
                            $display("Time: %0t  Instance: %m", $time);
                        end
                endcase
            end // if (lpm_mode == "READ")
            else if (lpm_mode == "WRITE")
            begin
                // verilator lint_off CASEX
                casex (sm_empty)
                // verilator lint_on CASEX
                    // state_empty
                    2'b00:
                        if (wreq)
                            sm_empty <= 2'b01;
                    // state_one
                    2'b01:
                        if (!wreq)
                            sm_empty <= 2'b11;
                    // state_non_empty
                    2'b11:
                        if (wreq)
                            sm_empty <= 2'b01;
                        else if (usedw_in == 0)
                            sm_empty <= 2'b00;
                    default:
                        begin
                            $display ("Error! Invalid sm_empty state in write mode.");
                            $display("Time: %0t  Instance: %m", $time);
                        end
                endcase
            end // if (lpm_mode == "WRITE")

            if (~aclr && (usedw_in >= almostfull) && ($time > 0))
                i_full <= 1'b1;
            else
                i_full <= 1'b0;
        end // if (~aclr && $time > 0)
    end // @(posedge clock)

    always @(sm_empty)
    begin
        i_empty <= !sm_empty[0];
    end
    // @(sm_empty)

// CONTINOUS ASSIGNMENT
    assign empty = i_empty;
    assign full = i_full;
endmodule // lpm_fifo_dc_fefifo
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_fifo_dc_async
//
// Description     :  Asynchronous Dual Clocks FIFO
//
// Limitation      :
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_fifo_dc_async (  data,
                            rdclk,
                            wrclk,
                            aclr,
                            rdreq,
                            wrreq,
                            rdfull,
                            wrfull,
                            rdempty,
                            wrempty,
                            rdusedw,
                            wrusedw,
                            q);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_widthu = 1;
    parameter lpm_numwords = 2;
    parameter delay_rdusedw = 1;
    parameter delay_wrusedw = 1;
    parameter rdsync_delaypipe = 3;
    parameter wrsync_delaypipe = 3;
    parameter lpm_showahead = "OFF";
    parameter underflow_checking = "ON";
    parameter overflow_checking = "ON";
    parameter lpm_hint = "INTENDED_DEVICE_FAMILY=Stratix";

// INPUT PORT DECLARATION
    input [lpm_width-1:0] data;
    input rdclk;
    input wrclk;
    input aclr;
    input wrreq;
    input rdreq;

// OUTPUT PORT DECLARATION
    output rdfull;
    output wrfull;
    output rdempty;
    output wrempty;
    output [lpm_widthu-1:0] rdusedw;
    output [lpm_widthu-1:0] wrusedw;
    output [lpm_width-1:0] q;

// INTERNAL REGISTERS DECLARATION
    reg [lpm_width-1:0] mem_data [(1<<lpm_widthu)-1:0];
    reg [lpm_width-1:0] i_data_tmp;
    reg [lpm_widthu-1:0] i_rdptr;
    reg [lpm_widthu-1:0] i_wrptr;
    reg [lpm_widthu-1:0] i_wrptr_tmp;
    reg i_rdenclock;
    reg i_wren_tmp;
    reg [lpm_widthu-1:0] i_wr_udwn;
    reg [lpm_widthu-1:0] i_rd_udwn;
    reg i_showahead_flag;
    reg i_showahead_flag1;
    reg [lpm_widthu:0] i_rdusedw;
    reg [lpm_widthu-1:0] i_wrusedw;
    reg [lpm_width-1:0] i_q_tmp;

    reg [8*5:1] i_overflow_checking;
    reg [8*5:1] i_underflow_checking;
    reg [8*10:1] use_eab;
    reg [8*20:1] intended_device_family;

// INTERNAL WIRE DECLARATION
    wire w_rden;
    wire w_wren;
    wire w_rdempty;
    wire w_wrempty;
    wire w_rdfull;
    wire w_wrfull;
    wire [lpm_widthu-1:0] w_rdptrrg;
    wire [lpm_widthu-1:0] w_wrdelaycycle;
    wire [lpm_widthu-1:0] w_ws_nbrp;
    wire [lpm_widthu-1:0] w_rs_nbwp;
    wire [lpm_widthu-1:0] w_ws_dbrp;
    wire [lpm_widthu-1:0] w_rs_dbwp;
    wire [lpm_widthu-1:0] w_rd_dbuw;
    wire [lpm_widthu-1:0] w_wr_dbuw;
    wire [lpm_widthu-1:0] w_rdusedw;
    wire [lpm_widthu-1:0] w_wrusedw;

// INTERNAL TRI DECLARATION
    tri0 aclr;

// LOCAL INTEGER DECLARATION
    integer i;

// COMPONENT INSTANTIATIONS
    LPM_DEVICE_FAMILIES dev ();
    LPM_HINT_EVALUATION eva();

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if((lpm_showahead != "ON") && (lpm_showahead != "OFF"))
        begin
            $display ("Error! lpm_showahead must be ON or OFF.");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        i_overflow_checking = eva.GET_PARAMETER_VALUE(lpm_hint, "OVERFLOW_CHECKING");
        if (i_overflow_checking == "")
        begin
            if ((overflow_checking != "ON") && (overflow_checking != "OFF"))
            begin
                $display ("Error! OVERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
                $display("Time: %0t  Instance: %m", $time);
                $stop;
            end
            else
                i_overflow_checking = overflow_checking;
        end
        else if ((i_overflow_checking != "ON") && (i_overflow_checking != "OFF"))
        begin
            $display ("Error! OVERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        i_underflow_checking = eva.GET_PARAMETER_VALUE(lpm_hint, "UNDERFLOW_CHECKING");
        if(i_underflow_checking == "")
        begin
            if ((underflow_checking != "ON") && (underflow_checking != "OFF"))
            begin
                $display ("Error! UNDERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
                $display("Time: %0t  Instance: %m", $time);
                $stop;
            end
            else
                i_underflow_checking = underflow_checking;
        end
        else if ((i_underflow_checking != "ON") && (i_underflow_checking != "OFF"))
        begin
            $display ("Error! UNDERFLOW_CHECKING must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        use_eab = eva.GET_PARAMETER_VALUE(lpm_hint, "USE_EAB");
        if(use_eab == "")
            use_eab = "ON";
        else if ((use_eab != "ON") && (use_eab != "OFF"))
        begin
            $display ("Error! USE_EAB must equal to either 'ON' or 'OFF'");
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        intended_device_family = eva.GET_PARAMETER_VALUE(lpm_hint, "INTENDED_DEVICE_FAMILY");
        if (intended_device_family == "")
            intended_device_family = "Stratix II";
        else if (dev.IS_VALID_FAMILY(intended_device_family) == 0)
        begin
            $display ("Error! Unknown INTENDED_DEVICE_FAMILY=%s.", intended_device_family);
            $display("Time: %0t  Instance: %m", $time);
            $stop;
        end

        for (i = 0; i < (1 << lpm_widthu); i = i + 1)
            mem_data[i] <= 0;
        i_data_tmp <= 0;
        i_rdptr <= 0;
        i_wrptr <= 0;
        i_wrptr_tmp <= 0;
        i_wren_tmp <= 0;
        i_wr_udwn <= 0;
        i_rd_udwn <= 0;

        i_rdusedw <= 0;
        i_wrusedw <= 0;
        i_q_tmp <= 0;
    end

// COMPONENT INSTANTIATIONS
    // Delays & DFF Pipes
    lpm_fifo_dc_dffpipe DP_RDPTR_D (
        .d (i_rdptr),
        .clock (i_rdenclock),
        .aclr (aclr),
        .q (w_rdptrrg));
    lpm_fifo_dc_dffpipe DP_WRPTR_D (
        .d (i_wrptr),
        .clock (wrclk),
        .aclr (aclr),
        .q (w_wrdelaycycle));
    defparam
        DP_RDPTR_D.lpm_delay = 0,
        DP_RDPTR_D.lpm_width = lpm_widthu,
        DP_WRPTR_D.lpm_delay = 1,
        DP_WRPTR_D.lpm_width = lpm_widthu;

    lpm_fifo_dc_dffpipe DP_WS_NBRP (
        .d (w_rdptrrg),
        .clock (wrclk),
        .aclr (aclr),
        .q (w_ws_nbrp));
    lpm_fifo_dc_dffpipe DP_RS_NBWP (
        .d (w_wrdelaycycle),
        .clock (rdclk),
        .aclr (aclr),
        .q (w_rs_nbwp));
    lpm_fifo_dc_dffpipe DP_WS_DBRP (
        .d (w_ws_nbrp),
        .clock (wrclk),
        .aclr (aclr),
        .q (w_ws_dbrp));
    lpm_fifo_dc_dffpipe DP_RS_DBWP (
        .d (w_rs_nbwp),
        .clock (rdclk),
        .aclr (aclr),
        .q (w_rs_dbwp));
    defparam
        DP_WS_NBRP.lpm_delay = wrsync_delaypipe,
        DP_WS_NBRP.lpm_width = lpm_widthu,
        DP_RS_NBWP.lpm_delay = rdsync_delaypipe,
        DP_RS_NBWP.lpm_width = lpm_widthu,
        DP_WS_DBRP.lpm_delay = 1,              // gray_delaypipe
        DP_WS_DBRP.lpm_width = lpm_widthu,
        DP_RS_DBWP.lpm_delay = 1,              // gray_delaypipe
        DP_RS_DBWP.lpm_width = lpm_widthu;

    lpm_fifo_dc_dffpipe DP_WRUSEDW (
        .d (i_wr_udwn),
        .clock (wrclk),
        .aclr (aclr),
        .q (w_wrusedw));
    lpm_fifo_dc_dffpipe DP_RDUSEDW (
        .d (i_rd_udwn),
        .clock (rdclk),
        .aclr (aclr),
        .q (w_rdusedw));
    lpm_fifo_dc_dffpipe DP_WR_DBUW (
        .d (i_wr_udwn),
        .clock (wrclk),
        .aclr (aclr),
        .q (w_wr_dbuw));
    lpm_fifo_dc_dffpipe DP_RD_DBUW (
        .d (i_rd_udwn),
        .clock (rdclk),
        .aclr (aclr),
        .q (w_rd_dbuw));
    defparam
        DP_WRUSEDW.lpm_delay = delay_wrusedw,
        DP_WRUSEDW.lpm_width = lpm_widthu,
        DP_RDUSEDW.lpm_delay = delay_rdusedw,
        DP_RDUSEDW.lpm_width = lpm_widthu,
        DP_WR_DBUW.lpm_delay = 1,              // wrusedw_delaypipe
        DP_WR_DBUW.lpm_width = lpm_widthu,
        DP_RD_DBUW.lpm_delay = 1,              // rdusedw_delaypipe
        DP_RD_DBUW.lpm_width = lpm_widthu;

    // Empty/Full
    lpm_fifo_dc_fefifo WR_FE (
        .usedw_in (w_wr_dbuw),
        .wreq (wrreq),
        .rreq (rdreq),
        .clock (wrclk),
        .aclr (aclr),
        .empty (w_wrempty),
        .full (w_wrfull));
    lpm_fifo_dc_fefifo RD_FE (
        .usedw_in (w_rd_dbuw),
        .rreq (rdreq),
        .wreq(wrreq),
        .clock (rdclk),
        .aclr (aclr),
        .empty (w_rdempty),
        .full (w_rdfull));
    defparam
        WR_FE.lpm_widthad = lpm_widthu,
        WR_FE.lpm_numwords = lpm_numwords,
        WR_FE.underflow_checking = underflow_checking,
        WR_FE.overflow_checking = overflow_checking,
        WR_FE.lpm_mode = "WRITE",
        WR_FE.lpm_hint = lpm_hint,
        RD_FE.lpm_widthad = lpm_widthu,
        RD_FE.lpm_numwords = lpm_numwords,
        RD_FE.underflow_checking = underflow_checking,
        RD_FE.overflow_checking = overflow_checking,
        RD_FE.lpm_mode = "READ",
        RD_FE.lpm_hint = lpm_hint;

// ALWAYS CONSTRUCT BLOCK
    always @(posedge aclr)
    begin
        i_rdptr <= 0;
        i_wrptr <= 0;
        if (!(dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
            dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family)) ||
            (use_eab == "OFF"))
            if (lpm_showahead == "ON")
                i_q_tmp <= mem_data[0];
            else
                i_q_tmp <= 0;
    end // @(posedge aclr)

    // FIFOram
    always @(posedge wrclk)
    begin
        if (aclr && (!(dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
        dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family)) ||
        (use_eab == "OFF")))
        begin
            i_data_tmp <= 0;
            i_wrptr_tmp <= 0;
            i_wren_tmp <= 0;
        end
        else if (wrclk && ($time > 0))
        begin
            i_data_tmp <= data;
            i_wrptr_tmp <= i_wrptr;
            i_wren_tmp <= w_wren;

            if (w_wren)
            begin
                if (~aclr && ((i_wrptr < (1<<lpm_widthu)-1) || (i_overflow_checking == "OFF")))
                    i_wrptr <= i_wrptr + 1;
                else
                    i_wrptr <= 0;

                if (use_eab == "OFF")
                begin
                    mem_data[i_wrptr] <= data;

                    if (lpm_showahead == "ON")
                        i_showahead_flag1 <= 1'b1;
                end
            end
        end
    end // @(posedge wrclk)

    always @(negedge wrclk)
    begin
        if ((~wrclk && (use_eab == "ON")) && ($time > 0))
        begin
            if (i_wren_tmp)
            begin
                mem_data[i_wrptr_tmp] <= i_data_tmp;
            end

            if (lpm_showahead == "ON")
                    i_showahead_flag1 <= 1'b1;
        end
    end // @(negedge wrclk)

    always @(posedge rdclk)
    begin
        if (aclr && (!(dev.FEATURE_FAMILY_BASE_STRATIX(intended_device_family) ||
        dev.FEATURE_FAMILY_BASE_CYCLONE(intended_device_family)) ||
        (use_eab == "OFF")))
        begin
            if (lpm_showahead == "ON")
                i_q_tmp <= mem_data[0];
            else
                i_q_tmp <= 0;
        end
        else if (rdclk && w_rden && ($time > 0))
        begin
            if (~aclr && ((i_rdptr < (1<<lpm_widthu)-1) || (i_underflow_checking == "OFF")))
                i_rdptr <= i_rdptr + 1;
            else
                i_rdptr <= 0;

            if (lpm_showahead == "ON")
                i_showahead_flag1 <= 1'b1;
            else
                i_q_tmp <= mem_data[i_rdptr];
        end
    end // @(rdclk)

    always @(posedge i_showahead_flag)
    begin
        i_q_tmp <= mem_data[i_rdptr];
        i_showahead_flag1 <= 1'b0;
    end // @(posedge i_showahead_flag)

    always @(i_showahead_flag1)
    begin
        i_showahead_flag <= i_showahead_flag1;
    end // @(i_showahead_flag1)

    // Delays & DFF Pipes
    always @(negedge rdclk)
    begin
        i_rdenclock <= 0;
    end // @(negedge rdclk)

    always @(posedge rdclk)
    begin
        if (w_rden)
            i_rdenclock <= 1;
    end // @(posedge rdclk)

    always @(i_wrptr or w_ws_dbrp)
    begin
        i_wr_udwn <= i_wrptr - w_ws_dbrp;
    end // @(i_wrptr or w_ws_dbrp)

    always @(i_rdptr or w_rs_dbwp)
    begin
        i_rd_udwn <= w_rs_dbwp - i_rdptr;
    end // @(i_rdptr or w_rs_dbwp)

// CONTINOUS ASSIGNMENT
    assign w_rden = (i_underflow_checking == "OFF") ? rdreq : rdreq && !w_rdempty;
    assign w_wren = (i_overflow_checking == "OFF")  ? wrreq : wrreq && !w_wrfull;
    assign q = i_q_tmp;
    assign wrfull = w_wrfull;
    assign rdfull = w_rdfull;
    assign wrempty = w_wrempty;
    assign rdempty = w_rdempty;
    assign wrusedw = w_wrusedw;
    assign rdusedw = w_rdusedw;

endmodule // lpm_fifo_dc_async
// END OF MODULE


//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_fifo_dc
//
// Description     :
//
// Limitation      :
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_fifo_dc (data,
                    rdclock,
                    wrclock,
                    aclr,
                    rdreq,
                    wrreq,
                    rdfull,
                    wrfull,
                    rdempty,
                    wrempty,
                    rdusedw,
                    wrusedw,
                    q);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_widthu = 1;
    parameter lpm_numwords = 2;
    parameter lpm_showahead = "OFF";
    parameter underflow_checking = "ON";
    parameter overflow_checking = "ON";
    parameter lpm_hint = "";
    parameter lpm_type = "lpm_fifo_dc";

// LOCAL PARAMETER DECLARATION
    parameter delay_rdusedw = 1;
    parameter delay_wrusedw = 1;
    parameter rdsync_delaypipe = 3;
    parameter wrsync_delaypipe = 3;

// INPUT PORT DECLARATION
    input [lpm_width-1:0] data;
    input rdclock;
    input wrclock;
    input aclr;
    input rdreq;
    input wrreq;

// OUTPUT PORT DECLARATION
    output rdfull;
    output wrfull;
    output rdempty;
    output wrempty;
    output [lpm_widthu-1:0] rdusedw;
    output [lpm_widthu-1:0] wrusedw;
    output [lpm_width-1:0] q;

// internal reg
    wire w_rdfull_s;
    wire w_wrfull_s;
    wire w_rdempty_s;
    wire w_wrempty_s;
    wire w_rdfull_a;
    wire w_wrfull_a;
    wire w_rdempty_a;
    wire w_wrempty_a;
    wire [lpm_widthu-1:0] w_rdusedw_s;
    wire [lpm_widthu-1:0] w_wrusedw_s;
    wire [lpm_widthu-1:0] w_rdusedw_a;
    wire [lpm_widthu-1:0] w_wrusedw_a;
    wire [lpm_width-1:0] w_q_s;
    wire [lpm_width-1:0] w_q_a;
    wire i_aclr;

// INTERNAL TRI DECLARATION
    tri0 aclr;
    buf (i_aclr, aclr);

// COMPONENT INSTANTIATIONS
    lpm_fifo_dc_async ASYNC (
        .data (data),
        .rdclk (rdclock),
        .wrclk (wrclock),
        .aclr (i_aclr),
        .rdreq (rdreq),
        .wrreq (wrreq),
        .rdfull (w_rdfull_a),
        .wrfull (w_wrfull_a),
        .rdempty (w_rdempty_a),
        .wrempty (w_wrempty_a),
        .rdusedw (w_rdusedw_a),
        .wrusedw (w_wrusedw_a),
        .q (w_q_a) );
    defparam
        ASYNC.lpm_width = lpm_width,
        ASYNC.lpm_widthu = lpm_widthu,
        ASYNC.lpm_numwords = lpm_numwords,
        ASYNC.delay_rdusedw = delay_rdusedw,
        ASYNC.delay_wrusedw = delay_wrusedw,
        ASYNC.rdsync_delaypipe = rdsync_delaypipe,
        ASYNC.wrsync_delaypipe = wrsync_delaypipe,
        ASYNC.lpm_showahead = lpm_showahead,
        ASYNC.underflow_checking = underflow_checking,
        ASYNC.overflow_checking = overflow_checking,
        ASYNC.lpm_hint = lpm_hint;

// CONTINOUS ASSIGNMENT
    assign rdfull =  w_rdfull_a;
    assign wrfull =  w_wrfull_a;
    assign rdempty = w_rdempty_a;
    assign wrempty = w_wrempty_a;
    assign rdusedw = w_rdusedw_a;
    assign wrusedw = w_wrusedw_a;
    assign q = w_q_a;
endmodule // lpm_fifo_dc
// END OF MODULE

//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_inpad
//
// Description     :
//
// Limitation      :  n/a
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_inpad (
    pad,
    result
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_type = "lpm_inpad";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] pad;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_width-1:0] result;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(pad)
    begin
        result = pad;
    end

endmodule // lpm_inpad
// END OF MODULE


//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_outpad
//
// Description     :
//
// Limitation      :  n/a
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_outpad (
    data,
    pad
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_type = "lpm_outpad";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] pad;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_width-1:0] pad;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data)
    begin
        pad = data;
    end

endmodule // lpm_outpad
// END OF MODULE


//START_MODULE_NAME------------------------------------------------------------
//
// Module Name     :  lpm_bipad
//
// Description     :
//
// Limitation      :  n/a
//
// Results expected:
//
//END_MODULE_NAME--------------------------------------------------------------

// BEGINNING OF MODULE
`timescale 1 ps / 1 ps

// MODULE DECLARATION
module lpm_bipad (
    data,
    enable,
    result,
    pad
);

// GLOBAL PARAMETER DECLARATION
    parameter lpm_width = 1;
    parameter lpm_type = "lpm_bipad";
    parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
    input  [lpm_width-1:0] data;
    input  enable;

// OUTPUT PORT DECLARATION
    output [lpm_width-1:0] result;

// INPUT/OUTPUT PORT DECLARATION
    inout  [lpm_width-1:0] pad;

// INTERNAL REGISTER/SIGNAL DECLARATION
    reg    [lpm_width-1:0] result;

// INITIAL CONSTRUCT BLOCK
    initial
    begin
        if (lpm_width <= 0)
        begin
            $display("Value of lpm_width parameter must be greater than 0(ERROR)");
            $display("Time: %0t  Instance: %m", $time);
            $finish;
        end
    end

// ALWAYS CONSTRUCT BLOCK
    always @(data or pad or enable)
    begin
        if (enable == 1)
        begin
            result = {lpm_width{1'bz}};
        end
        else if (enable == 0)
        begin
            result = pad;
        end
    end

// CONTINOUS ASSIGNMENT
    assign pad = (enable == 1) ? data : {lpm_width{1'bz}};

endmodule // lpm_bipad
// END OF MODULE
