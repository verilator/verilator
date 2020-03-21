// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// Overview of files involved in parsing
//       V3Parse.h              External consumer interface to V3ParseImp
//       V3ParseImp             Internals to parser, common to across flex & bison
//         V3ParseGrammar       Wrapper that includes V3ParseBison
//           V3ParseBison       Bison output
//         V3ParseLex           Wrapper that includes lex output
//           V3Lexer.yy.cpp     Flex output
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3Os.h"
#include "V3Ast.h"
#include "V3File.h"
#include "V3ParseImp.h"
#include "V3PreShell.h"
#include "V3LanguageWords.h"

#include <cstdarg>
#include <fstream>
#include <sstream>

//======================================================================
// Globals

V3ParseImp*     V3ParseImp::s_parsep = NULL;

int             V3ParseSym::s_anonNum = 0;

extern void yyerror(const char*);
extern void yyerrorf(const char* format, ...);

//######################################################################
// Parser constructor

V3ParseImp::~V3ParseImp() {
    for (std::deque<string*>::iterator it = m_stringps.begin(); it != m_stringps.end(); ++it) {
        VL_DO_DANGLING(delete *it, *it);
    }
    m_stringps.clear();
    for (std::deque<V3Number*>::iterator it = m_numberps.begin(); it != m_numberps.end(); ++it) {
        VL_DO_DANGLING(delete *it, *it);
    }
    m_numberps.clear();
    lexDestroy();
    parserClear();

    if (debug()>=9) { UINFO(0,"~V3ParseImp\n"); symp()->dump(cout, "-vpi: "); }
}

//######################################################################
// Parser utility methods

void V3ParseImp::ppline(const char* textp) {
    // Handle `line directive
    FileLine* prevFl = copyOrSameFileLine();
    int enterExit;
    fileline()->lineDirective(textp, enterExit/*ref*/);
    if (enterExit == 1) {  // Enter
        fileline()->parent(prevFl);
    } else if (enterExit == 2) {  // Exit
        FileLine* upFl = fileline()->parent();
        if (upFl) upFl = upFl->parent();
        if (upFl) fileline()->parent(upFl);
    }
}

void V3ParseImp::verilatorCmtLintSave() {
    m_lintState.push_back(*parsep()->fileline());
}

void V3ParseImp::verilatorCmtLintRestore() {
    if (m_lintState.empty()) {
        yyerrorf("/*verilator lint_restore*/ without matching save.");
        return;
    }
    parsep()->fileline()->warnStateFrom(m_lintState.back());
    m_lintState.pop_back();
}

void V3ParseImp::verilatorCmtLint(const char* textp, bool warnOff) {
    const char* sp = textp;
    while (*sp && !isspace(*sp)) sp++;
    while (*sp && isspace(*sp)) sp++;
    while (*sp && !isspace(*sp)) sp++;
    while (*sp && isspace(*sp)) sp++;
    string msg = sp;
    string::size_type pos;
    if ((pos = msg.find('*')) != string::npos) { msg.erase(pos); }
    if (!(parsep()->fileline()->warnOff(msg, warnOff))) {
        if (!parsep()->optFuture(msg)) {
            yyerrorf("Unknown verilator lint message code: %s, in %s", msg.c_str(), textp);
        }
    }
}

void V3ParseImp::verilatorCmtBad(const char* textp) {
    string cmtparse = textp;
    if (cmtparse.substr(0, strlen("/*verilator")) == "/*verilator") {
        cmtparse.replace(0, strlen("/*verilator"), "");
    }
    while (isspace(cmtparse[0])) {
        cmtparse.replace(0, 1, "");
    }
    string cmtname;
    for (int i = 0; isalnum(cmtparse[i]); i++) {
        cmtname += cmtparse[i];
    }
    if (!parsep()->optFuture(cmtname)) {
        yyerrorf("Unknown verilator comment: %s", textp);
    }
}

void V3ParseImp::errorPreprocDirective(const char* textp) {
    // Find all `preprocessor spelling candidates
    // Can't make this static as might get more defines later when read cells
    VSpellCheck speller;
    V3LanguageWords words;
    for (V3LanguageWords::const_iterator it = words.begin(); it != words.end(); ++it) {
        string ppDirective = it->first;
        if (ppDirective[0] == '`') speller.pushCandidate(ppDirective);
    }
    V3PreShell::candidateDefines(&speller);
    string suggest = speller.bestCandidateMsg(textp);
    fileline()->v3error("Define or directive not defined: '"<<textp<<"'\n"
                        <<(suggest.empty() ? "" : fileline()->warnMore()+suggest));
}

void V3ParseImp::tag(const char* text) {
    if (m_tagNodep) {
        string tmp = text + strlen("/*verilator tag ");
        string::size_type pos;
        if ((pos = tmp.rfind("*/")) != string::npos) { tmp.erase(pos); }
        m_tagNodep->tag(tmp);
    }
}

double V3ParseImp::parseDouble(const char* textp, size_t length, bool* successp) {
    char* strgp = new char[length+1];
    char* dp = strgp;
    if (successp) *successp = true;
    for (const char* sp = textp; sp < (textp+length); ++sp) {
        if (*sp != '_') *dp++ = *sp;
    }
    *dp++ = '\0';
    char* endp = strgp;
    double d = strtod(strgp, &endp);
    size_t parsed_len = endp-strgp;
    if (parsed_len != strlen(strgp)) {
        if (successp) *successp = false;
        else yyerrorf("Syntax error parsing real: %s", strgp);
    }
    VL_DO_DANGLING(delete[] strgp, strgp);
    return d;
}

//######################################################################
// Parser tokenization

size_t V3ParseImp::ppInputToLex(char* buf, size_t max_size) {
    size_t got = 0;
    while (got < max_size  // Haven't got enough
           && !m_ppBuffers.empty()) {  // And something buffered
        string front = m_ppBuffers.front(); m_ppBuffers.pop_front();
        size_t len = front.length();
        if (len > (max_size-got)) {  // Front string too big
            string remainder = front.substr(max_size-got);
            front = front.substr(0, max_size-got);
            m_ppBuffers.push_front(remainder);  // Put back remainder for next time
            len = (max_size-got);
        }
        memcpy(buf+got, front.c_str(), len);
        got += len;
    }
    if (debug()>=9) {
        string out = string(buf, got);
        cout<<"   inputToLex  got="<<got<<" '"<<out<<"'"<<endl;
    }
    // Note returns 0 at EOF
    return got;
}

void V3ParseImp::preprocDumps(std::ostream& os) {
    if (v3Global.opt.dumpDefines()) {
        V3PreShell::dumpDefines(os);
    } else {
        bool noblanks = v3Global.opt.preprocOnly() && v3Global.opt.preprocNoLine();
        for (std::deque<string>::iterator it = m_ppBuffers.begin(); it!=m_ppBuffers.end(); ++it) {
            if (noblanks) {
                bool blank = true;
                for (string::iterator its = it->begin(); its != it->end(); ++its) {
                    if (!isspace(*its) && *its!='\n') { blank = false; break; }
                }
                if (blank) continue;
            }
            os << *it;
        }
    }
}

void V3ParseImp::parseFile(FileLine* fileline, const string& modfilename, bool inLibrary,
                           const string& errmsg) {  // "" for no error, make fake node
    string modname = V3Os::filenameNonExt(modfilename);

    UINFO(2,__FUNCTION__<<": "<<modname<<(inLibrary?" [LIB]":"")<<endl);
    m_fileline = new FileLine(fileline);
    m_fileline->newContent();
    m_inLibrary = inLibrary;

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
        std::ofstream* ofp = NULL;
        std::ostream* osp;
        if (v3Global.opt.preprocOnly()) {
            osp = &cout;
        } else {
            osp = ofp = V3File::new_ofstream(vppfilename);
        }
        if (osp->fail()) {
            fileline->v3error("Cannot write preprocessor output: "+vppfilename);
            return;
        } else {
            preprocDumps(*osp);
            if (ofp) {
                ofp->close();
                VL_DO_DANGLING(delete ofp, ofp);
            }
        }
    }

    // Parse it
    if (!v3Global.opt.preprocOnly()) {
        lexFile(modfilename);
    } else {
        m_ppBuffers.clear();
    }
}

void V3ParseImp::lexFile(const string& modname) {
    // Prepare for lexing
    UINFO(3,"Lexing "<<modname<<endl);
    s_parsep = this;
    fileline()->warnResetDefault();  // Reenable warnings on each file
    lexDestroy();  // Restart from clean slate.
    lexNew();

    // Lex it
    if (bisonParse()) v3fatal("Cannot continue\n");
}

//======================================================================
// V3Parse functions

V3Parse::V3Parse(AstNetlist* rootp, VInFilter* filterp, V3ParseSym* symp) {
    m_impp = new V3ParseImp(rootp, filterp, symp);
}
V3Parse::~V3Parse() {
    VL_DO_CLEAR(delete m_impp, m_impp = NULL);
}
void V3Parse::parseFile(FileLine* fileline, const string& modname, bool inLibrary,
                        const string& errmsg) {
    m_impp->parseFile(fileline, modname, inLibrary, errmsg);
}
void V3Parse::ppPushText(V3ParseImp* impp, const string& text) {
    if (text != "") impp->ppPushText(text);
}
