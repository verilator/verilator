// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_replay: Command line options
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2020 by Todd Strader.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "VlrOptions.h"
#include "config_build.h"
#include "config_rev.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3Os.h"
#include <memory>
#include <fstream>

void VlrOptions::parseOptsList(int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    for (int i=0; i<argc; )  {
        UINFO(9, " Option: "<<argv[i]<<endl);
        if (argv[i][0]=='-') {
            const char* sw = argv[i];
            bool flag = true;
            // Allow gnu -- switches
            if (sw[0]=='-' && sw[1]=='-') ++sw;
            if (0) {} // TODO -- just to avoid the asymetry of one "if"?
            // Single switches
            else if (onoff (sw, "-vlt", flag/*ref*/) )      { m_vlt = flag; }
            //// Parameterized switches
            else if (!strcmp(sw, "-debug") ) {
                V3Error::debugDefault(3);
            }
            else if (!strcmp(sw, "-debugi") && (i+1)<argc ) {
                ++i;
                V3Error::debugDefault(atoi(argv[i]));
            }
            else if (!strcmp(sw, "-fst") && (i+1)<argc ) {
                ++i;
                m_fst = argv[i];
            }
            else if (!strcmp(sw, "-replay-top") && (i+1)<argc ) {
                ++i;
                m_replayTop= argv[i];
            }
            else if (!strcmp(sw, "-scope") && (i+1)<argc ) {
                ++i;
                m_scope = argv[i];
            }
            else if (!strcmp(sw, "-signal-list") && (i+1)<argc ) {
                ++i;
                readSignalList(argv[i]);
            }
            else if (!strcmp(sw, "-V") ) {
                showVersion(true);
                exit(0);
            }
            else if (!strcmp(sw, "-version") ) {
                showVersion(false);
                exit(0);
            }
            else {
                v3fatal("Invalid option: "<<argv[i]);
            }
            ++i;
        }  // - options
        //else if (1) {
        //    addReadFile(argv[i]);
        //    ++i;
        //}
        else {
            v3fatal("Invalid argument: "<<argv[i]);
            ++i;
        }
    }
}

void VlrOptions::showVersion(bool verbose) {
    cout <<version();
    cout <<endl;
    if (!verbose) return;

    cout <<endl;
    cout << "Copyright 2020 by Todd Strader.  Verilator is free software; you can\n";
    cout << "redistribute it and/or modify the Verilator internals under the terms of\n";
    cout << "either the GNU Lesser General Public License Version 3 or the Perl Artistic\n";
    cout << "License Version 2.0.\n";

    cout <<endl;
    cout << "See https://verilator.org for documentation\n";
}

string VlrOptions::version() {
    string ver = DTVERSION;
    ver += " rev "+cvtToStr(DTVERSION_rev);
    return ver;
}

// TODO -- Shared with Verilator too?  Refactor into some common code.
bool VlrOptions::onoff(const char* sw, const char* arg, bool& flag) {
    // if sw==arg, then return true (found it), and flag=true
    // if sw=="-no-arg", then return true (found it), and flag=false
    // if sw=="-noarg", then return true (found it), and flag=false
    // else return false
    if (arg[0]!='-') v3fatalSrc("OnOff switches must have leading dash.");
    if (0==strcmp(sw, arg)) { flag = true; return true; }
    else if (0==strncmp(sw, "-no", 3) && (0==strcmp(sw+3, arg+1))) { flag = false; return true; }
    else if (0==strncmp(sw, "-no-", 4) && (0==strcmp(sw+4, arg+1))) { flag = false; return true; }
    return false;
}

void VlrOptions::readSignalList(const char* filename) {
    std::ifstream ifs(filename);
    if (ifs.fail()) {
        v3fatal("Cannot open -f command file: "+string(filename));
        return;
    }

    while (!ifs.eof()) {
        string line = V3Os::getline(ifs);

        // Remove comments
        size_t cmt = line.find("#");
        if (cmt == 0) {
            continue;
        } else if (cmt != string::npos) {
            line = line.substr(0, cmt);
        }

        // Parse signals
        if (line.length() <= 2) continue;

        string signalName = line.substr(2);

        if (line.substr(0, 2) == "I ") {
            m_replayp->addInputName(signalName);
        } else if (line.substr(0, 2) == "O ") {
            m_replayp->addOutputName(signalName);
        } else {
            v3fatal("Invalid signal line: "+line);
        }
    }
}
