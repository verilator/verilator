// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
// Overview of files involved in parsing
//	 V3Parse.h		External consumer interface to V3ParseImp
//	 V3ParseImp		Internals to parser, common to across flex & bison
//	   V3ParseGrammar	Wrapper that includes V3ParseBison
//	     V3ParseBison	Bison output
//	   V3ParseLex		Wrapper that includes lex output
//	     V3Lexer.yy.cpp	Flex output
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <fstream>
#include <sstream>

#include "V3Error.h"
#include "V3Global.h"
#include "V3Os.h"
#include "V3Ast.h"
#include "V3File.h"
#include "V3ParseImp.h"
#include "V3PreShell.h"

//======================================================================
// Globals

V3ParseImp*	V3ParseImp::s_parsep = NULL;

int		V3ParseSym::s_anonNum = 0;

//######################################################################
// Read class functions

V3ParseImp::~V3ParseImp() {
    for (deque<string*>::iterator it = m_stringps.begin(); it != m_stringps.end(); ++it) {
	delete (*it);
    }
    m_stringps.clear();
    for (deque<V3Number*>::iterator it = m_numberps.begin(); it != m_numberps.end(); ++it) {
	delete (*it);
    }
    m_numberps.clear();
    lexDestroy();
    parserClear();

    if (debug()>=9) { UINFO(0,"~V3ParseImp\n"); symp()->dump(cout, "-vpi: "); }
}

size_t V3ParseImp::ppInputToLex(char* buf, size_t max_size) {
    size_t got = 0;
    while (got < max_size	// Haven't got enough
	   && !m_ppBuffers.empty()) {	// And something buffered
	string front = m_ppBuffers.front(); m_ppBuffers.pop_front();
	size_t len = front.length();
	if (len > (max_size-got)) {  // Front string too big
	    string remainder = front.substr(max_size-got);
	    front = front.substr(0, max_size-got);
	    m_ppBuffers.push_front(remainder);  // Put back remainder for next time
	    len = (max_size-got);
	}
	strncpy(buf+got, front.c_str(), len);
	got += len;
    }
    if (debug()>=9) {
	string out = string(buf,got);
	cout<<"   inputToLex  got="<<got<<" '"<<out<<"'"<<endl;
    }
    // Note returns 0 at EOF
    return got;
}

void V3ParseImp::parseFile(FileLine* fileline, const string& modfilename, bool inLibrary,
			   const string& errmsg) {  // "" for no error, make fake node
    string modname = V3Os::filenameNonExt(modfilename);

    UINFO(2,__FUNCTION__<<": "<<modname<<(inLibrary?" [LIB]":"")<<endl);
    m_fileline = new FileLine(fileline);
    m_inLibrary = inLibrary;

    // Set language standard up front
    if (!v3Global.opt.preprocOnly()) {
	// Leting lex parse this saves us from having to specially en/decode
	// from the V3LangCode to the various Lex BEGIN states. The language
	// of this source file is updated here, in case there have been any
	// intervening +<lang>ext+ options since it was first ecountered.
	FileLine *modfileline = new FileLine (modfilename, 0);
	modfileline->language(v3Global.opt.fileLanguage(modfilename));
	ppPushText((string)"`begin_keywords \""+modfileline->language().ascii()+"\"\n");
    }

    // Preprocess into m_ppBuffer
    bool ok = V3PreShell::preproc(fileline, modfilename, m_filterp, this, errmsg);
    if (!ok) {
	if (errmsg != "") return;  // Threw error already
	// Create fake node for later error reporting
	AstNodeModule* nodep = new AstNotFoundModule(fileline, modname);
	v3Global.rootp()->addModulep(nodep);
	return;
    }

    if (v3Global.opt.preprocOnly() || v3Global.opt.keepTempFiles()) {
	// Create output file with all the preprocessor output we buffered up
	string vppfilename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_"+modname+".vpp";
	ofstream* ofp = NULL;
	ostream* osp;
	bool noblanks = v3Global.opt.preprocOnly() && v3Global.opt.preprocNoLine();
	if (v3Global.opt.preprocOnly()) {
	    osp = &cout;
	} else {
	    osp = ofp = V3File::new_ofstream(vppfilename);
	}
	if (osp->fail()) {
	    fileline->v3error("Cannot write preprocessor output: "+vppfilename);
	    return;
	} else {
	    for (deque<string>::iterator it = m_ppBuffers.begin(); it!=m_ppBuffers.end(); ++it) {
		if (noblanks) {
		    bool blank = true;
		    for (string::iterator its = it->begin(); its != it->end(); ++its) {
			if (!isspace(*its) && *its!='\n') { blank=false; break; }
		    }
		    if (blank) continue;
		}
		*osp << *it;
	    }
	    if (ofp) {
		ofp->close();
		delete ofp; ofp = NULL;
	    }
	}
    }

    // Parse it
    if (!v3Global.opt.preprocOnly()) {
	lexFile (modfilename);
    }
}

void V3ParseImp::lexFile(const string& modname) {
    // Prepare for lexing
    UINFO(3,"Lexing "<<modname<<endl);
    s_parsep = this;
    fileline()->warnResetDefault();	// Reenable warnings on each file
    lexDestroy();	// Restart from clean slate.
    lexNew(debugFlex()>=9);

    // Lex it
    if (bisonParse()) v3fatal("Cannot continue\n");
}

//======================================================================
// V3Parse functions

V3Parse::V3Parse(AstNetlist* rootp, V3InFilter* filterp, V3ParseSym* symp) {
    m_impp = new V3ParseImp (rootp, filterp, symp);
}
V3Parse::~V3Parse() {
    delete m_impp; m_impp = NULL;
}
void V3Parse::parseFile(FileLine* fileline, const string& modname, bool inLibrary,
			const string& errmsg) {
    m_impp->parseFile(fileline, modname, inLibrary, errmsg);
}
void V3Parse::ppPushText(V3ParseImp* impp, const string& text) {
    impp->ppPushText(text);
}
