//*************************************************************************
// DESCRIPTION: Verilator: File stream wrapper that understands indentation
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2010 by Wilson Snyder.  This program is free software; you can
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdarg>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <iomanip>
#include <memory>

#include "V3Global.h"
#include "V3File.h"
#include "V3PreShell.h"
#include "V3Ast.h"

//######################################################################
// V3File Internal state

class V3FileDependImp {
    // TYPES
    class DependFile {
	// A single file
	bool		m_target;	// True if write, else read
	string		m_filename;	// Filename
	struct stat	m_stat;		// Stat information
    public:
	DependFile(const string& filename, bool target)
	    : m_target(target), m_filename(filename) {
	    m_stat.st_mtime = 0;
	}
	~DependFile() {}
	const string& filename() const { return m_filename; }
	bool target() const { return m_target; }
	off_t size() const { return m_stat.st_size; }
	time_t mtime() const { return m_stat.st_mtime; }
	void loadStats() {
	    if (!m_stat.st_mtime) {
		int err = stat(filename().c_str(), &m_stat);
		if (err!=0) {
		    m_stat.st_mtime = 1;
		    // Not a error... This can occur due to `line directives in the .vpp files
		    UINFO(1,"-Info: File not statable: "<<filename()<<endl);
		}
	    }
	}
	bool operator<(const DependFile& rhs) const { return filename()<rhs.filename(); }
    };

    // MEMBERS
    set<string>		m_filenameSet;		// Files generated (elim duplicates)
    set<DependFile>	m_filenameList;		// Files sourced/generated

    static string stripQuotes(const string& in) {
	string pretty = in;
	string::size_type pos;
	while ((pos=pretty.find("\"")) != string::npos) pretty.replace(pos, 1, "_");
	while ((pos=pretty.find("\n")) != string::npos) pretty.replace(pos, 1, "_");
	return pretty;
    }
public:
    // ACCESSOR METHODS
    void addSrcDepend(const string& filename) {
	if (m_filenameSet.find(filename) == m_filenameSet.end()) {
	    m_filenameSet.insert(filename);
	    DependFile df (filename, false);
	    df.loadStats();  // Get size now, in case changes during the run
	    m_filenameList.insert(df);
	}
    }
    void addTgtDepend(const string& filename) {
	if (m_filenameSet.find(filename) == m_filenameSet.end()) {
	    m_filenameSet.insert(filename);
	    m_filenameList.insert(DependFile (filename, true));
	}
    }
    void writeDepend(const string& filename);
    void writeTimes(const string& filename, const string& cmdline);
    bool checkTimes(const string& filename, const string& cmdline);
};

V3FileDependImp  dependImp;	// Depend implementation class

//######################################################################
// V3FileDependImp

inline void V3FileDependImp::writeDepend(const string& filename) {
    const auto_ptr<ofstream> ofp (V3File::new_ofstream(filename));
    if (ofp->fail()) v3fatalSrc("Can't write "<<filename);

    for (set<DependFile>::iterator iter=m_filenameList.begin();
	 iter!=m_filenameList.end(); ++iter) {
	if (iter->target()) {
	    *ofp<<iter->filename()<<" ";
	}
    }
    *ofp<<" : ";
    *ofp<<v3Global.opt.bin();
    *ofp<<" ";
    *ofp<<V3PreShell::dependFiles();
    *ofp<<"  ";

    for (set<DependFile>::iterator iter=m_filenameList.begin();
	 iter!=m_filenameList.end(); ++iter) {
	if (!iter->target()) {
	    *ofp<<iter->filename()<<" ";
	}
    }

    *ofp<<endl;

    if (v3Global.opt.makePhony()) {
	*ofp<<endl;
	for (set<DependFile>::iterator iter=m_filenameList.begin();
	     iter!=m_filenameList.end(); ++iter) {
	    if (!iter->target()) {
		*ofp<<iter->filename()<<":"<<endl;
	    }
	}
    }
}

inline void V3FileDependImp::writeTimes(const string& filename, const string& cmdlineIn) {
    const auto_ptr<ofstream> ofp (V3File::new_ofstream(filename));
    if (ofp->fail()) v3fatalSrc("Can't write "<<filename);

    string cmdline = stripQuotes(cmdlineIn);
    *ofp<<"# DESCR"<<"IPTION: Verilator output: Timestamp data for --skip-identical.  Delete at will."<<endl;
    *ofp<<"C \""<<cmdline<<"\""<<endl;

#if !defined (__MINGW32__)
    sync();  // Push files so sizes look correct
#endif
    for (set<DependFile>::iterator iter=m_filenameList.begin();
	 iter!=m_filenameList.end(); ++iter) {
	// Read stats of files we create after we're done making them (execpt for this file, of course)
	DependFile* dfp = (DependFile*)&(*iter);
	dfp->loadStats();
	off_t showSize = iter->size();
	if (dfp->filename() == filename) showSize=0;  // We're writing it, so need to ignore it

	*ofp<<(iter->target()?"T":"S")<<" ";
	*ofp<<" "<<setw(8)<<showSize;
	*ofp<<" "<<setw(11)<<iter->mtime();
	*ofp<<" \""<<iter->filename()<<"\"";
	*ofp<<endl;
    }
}

inline bool V3FileDependImp::checkTimes(const string& filename, const string& cmdlineIn) {
    const auto_ptr<ifstream> ifp (V3File::new_ifstream_nodepend(filename));
    if (ifp->fail()) {
	UINFO(2,"   --check-times failed: no input "<<filename<<endl);
	return false;
    }
    {
	string ignore;  getline(*ifp, ignore);
    }
    {
	char   chkDir;   *ifp>>chkDir;
	char   quote;    *ifp>>quote;
	string chkCmdline;  getline(*ifp, chkCmdline, '"');
	string cmdline = stripQuotes(cmdlineIn);
	if (cmdline != chkCmdline) {
	    UINFO(2,"   --check-times failed: different command line\n");
	    return false;
	}
    }

    while (!ifp->eof()) {
	char   chkDir;   *ifp>>chkDir;
	off_t  chkSize;  *ifp>>chkSize;
	if (ifp->eof()) break;  // Needed to read final whitespace before found eof
	time_t chkMtime; *ifp>>chkMtime;
	char   quote;    *ifp>>quote;
	string chkFilename; getline(*ifp, chkFilename, '"');
	//UINFO(9," got d="<<chkDir<<" s="<<chkSize<<" mt="<<chkMtime<<" fn = "<<chkFilename<<endl);

	struct stat chkStat;
	int err = stat(chkFilename.c_str(), &chkStat);
	if (err!=0) {
	    UINFO(2,"   --check-times failed: missing "<<chkFilename<<endl);
	    return false;
	}
	if (filename != chkFilename) {  // See above; we were writing it at the time...
	    // We'd like this rule:
	    //if (!(chkStat.st_size == chkSize
	    //      && chkStat.st_mtime == chkMtime) {
	    // However NFS messes us up, as there might be some data outstanding when
	    // we determined the original size.  For safety, we know the creation time
	    // must be within a few second window... call it 20 sec.
	    if (!(chkStat.st_size >= chkSize
		  && chkStat.st_mtime >= chkMtime
		  && chkStat.st_mtime <= (chkMtime + 20))) {
		UINFO(2,"   --check-times failed: out-of-date "<<chkFilename
		      <<"; "<<chkStat.st_size<<"=?"<<chkSize
		      <<" "<<chkStat.st_mtime<<"=?"<<chkMtime<<endl);
		return false;
	    }
	}
    }
    return true;
}

//######################################################################
// V3File

void V3File::addSrcDepend(const string& filename) {
    dependImp.addSrcDepend(filename);
}
void V3File::addTgtDepend(const string& filename) {
    dependImp.addTgtDepend(filename);
}
void V3File::writeDepend(const string& filename) {
    dependImp.writeDepend(filename);
}
void V3File::writeTimes(const string& filename, const string& cmdline) {
    dependImp.writeTimes(filename, cmdline);
}
bool V3File::checkTimes(const string& filename, const string& cmdline) {
    return dependImp.checkTimes(filename, cmdline);
}

void V3File::createMakeDir() {
    static bool created = false;
    if (!created) {
	created = true;
#if !defined (__MINGW32__)
	mkdir(v3Global.opt.makeDir().c_str(), 0777);
#else
	mkdir(v3Global.opt.makeDir().c_str());
#endif
    }
}

//######################################################################
// V3OutFormatter: A class for printing to a file, with automatic indentation of C++ code.

V3OutFormatter::V3OutFormatter(const string& filename, bool verilog)
    : m_filename(filename), m_verilog(verilog)
    , m_lineno(1), m_column(0)
    , m_nobreak(false), m_prependIndent(true), m_indentLevel(0)
    , m_declSAlign(0), m_declNSAlign(0), m_declPadNum(0) {
}

//----------------------------------------------------------------------

const char* V3OutFormatter::indentStr(int num) {
    // Indent the specified number of spaces.  Use tabs as possible.
    static char str[MAXSPACE+20];
    char* cp = str;
    if (num>MAXSPACE) num=MAXSPACE;
    if (!m_verilog) {  // verilogPrefixedTree doesn't want tabs
	while (num>=8) {
	    *cp++ = '\t';
	    num -= 8;
	}
    }
    while (num>0) {
	*cp++ = ' ';
	num --;
    }
    *cp++ = '\0';
    return (str);
}

const string V3OutFormatter::indentSpaces(int num) {
    // Indent the specified number of spaces.  Use spaces.
    static char str[MAXSPACE+20];
    char* cp = str;
    if (num>MAXSPACE) num=MAXSPACE;
    while (num>0) {
	*cp++ = ' ';
	num --;
    }
    *cp++ = '\0';
    string st (str);
    return (st);
}

bool V3OutFormatter::tokenStart(const char* cp, const char* cmp) {
    while (*cmp == *cp) { cp++; cmp++; }
    if (*cmp) return false;
    if (*cp && !isspace(*cp)) return false;
    return true;
}

bool V3OutFormatter::tokenEnd(const char* cp) {
    return (tokenStart(cp,"end")
	    || tokenStart(cp,"endcase")
	    || tokenStart(cp,"endmodule"));
}

int V3OutFormatter::endLevels (const char *strg) {
    int levels=m_indentLevel;
    const char* cp=strg;
    while (isspace(*cp)) cp++;
    switch (*cp) {
    case '\n':  // Newlines.. No need for whitespace before it
	return (0);
    case '#':	// Preproc directive
	return (0);
    }
    {
	// label/public/private:  Deindent by 2 spaces
	const char* mp=cp;
	for (; isalnum(*mp); mp++) ;
	if (mp[0]==':' && mp[1]!=':') return (levels-INDBLK/2);
    }

    // We want "} else {" to be one level to the left of normal
    for (const char* cp=strg; *cp; cp++) {
	switch (*cp) {
	case '}':
	case ')':
	    levels-=INDBLK;
	    break;
	case 'e':
	    if (m_verilog && tokenEnd(cp)) {
		levels-=INDBLK;
	    }
	    break;
	case '\t':
	case ' ':
	    break;  // Continue
	default:
	    return (levels);  // Letter
	}
    }
    return (levels);
}

void V3OutFormatter::puts (const char *strg) {
    if (m_prependIndent) {
	putsNoTracking(indentStr(endLevels(strg)));
	m_prependIndent = false;
    }
    bool wordstart = true;
    for (const char* cp=strg; *cp; cp++) {
	putcNoTracking (*cp);
	switch (*cp) {
	case '\n':
	    m_lineno++;
	    wordstart = true;
	    if (cp[1]=='\0') {
		m_prependIndent = true;	// Add the indent later, may be a indentInc/indentDec called between now and then
	    } else {
		m_prependIndent = false;
		putsNoTracking(indentStr(endLevels(cp+1)));
	    }
	    break;
	case ' ':
	    wordstart = true;
	    break;
	case '\t':
	    wordstart = true;
	    break;
	case '{':
	    indentInc();
	    break;
	case '(':
	    indentInc();
	    m_parenVec.push(m_column);
	    break;
	case '}':
	    indentDec();
	    break;
	case ')':
	    if (!m_parenVec.empty()) m_parenVec.pop();
	    indentDec();
	    break;
	case 'b':
	    if (wordstart && m_verilog && tokenStart(cp,"begin")) {
		indentInc();
	    }
	    wordstart = false;
	    break;
	case 'c':
	    if (wordstart && m_verilog && (tokenStart(cp,"case")
					   || tokenStart(cp,"casex")
					   || tokenStart(cp,"casez"))) {
		indentInc();
	    }
	    wordstart = false;
	    break;
	case 'e':
	    if (wordstart && m_verilog && tokenEnd(cp)) {
		indentDec();
	    }
	    wordstart = false;
	    break;
	case 'm':
	    if (wordstart && m_verilog && tokenStart(cp,"module")) {
		indentInc();
	    }
	    wordstart = false;
	    break;
	default:
	    wordstart = false;
	    break;
	}
    }
}

void V3OutFormatter::putBreakExpr () {
    if (!m_parenVec.empty()) putBreak();
}

// Add a line break if too wide
void V3OutFormatter::putBreak () {
    if (!m_nobreak) {
	//char s[1000]; sprintf(s,"{%d,%d}",m_column,m_parenVec.top()); putsNoTracking(s);
	if (exceededWidth()) {
	    putcNoTracking('\n');
	    if (!m_parenVec.empty()) putsNoTracking(indentStr(m_parenVec.top()));
	}
    }
}

void V3OutFormatter::putsQuoted(const char* strg) {
    // Quote \ and " for use inside C programs
    // Don't use to quote a filename for #include - #include doesn't \ escape.
    putcNoTracking('"');
    string quoted = AstNode::quoteName(strg);
    for (const char* cp=quoted.c_str(); *cp; cp++) {
	putcNoTracking (*cp);
    }
    putcNoTracking('"');
}
void V3OutFormatter::putsNoTracking (const char *strg) {
    // Don't track {}'s, probably because it's a $display format string
    for (const char* cp=strg; *cp; cp++) {
	putcNoTracking (*cp);
    }
}

void V3OutFormatter::putcNoTracking (char chr) {
    switch (chr) {
    case '\n':
	m_lineno++;
	m_column=0;
	m_nobreak=true;
	break;
    case '\t':
	m_column = ((m_column + 9)/8)*8;
	break;
    case ' ':
    case '(':
    case '|':
    case '&':
	m_column++;
	break;
    default:
	m_column++;
	m_nobreak=false;
	break;
    }
    putcOutput (chr);
}

void V3OutFormatter::putAlign (bool/*AlignClass*/ isStatic, int align, int size, const char* prefix) {
    if (size==0) size=align;
    int alignSize = size; if (alignSize>8) alignSize=8;
    int& alignr = isStatic ? m_declSAlign : m_declNSAlign;
    int padsize = alignSize - (alignr % alignSize);
    if (padsize && padsize!=alignSize) {
	// Modern versions of GCC no longer need this, they'll pad for us, so
	// we'll save the work and danger of getting it wrong.
	puts("//char\t");
	puts(prefix);
	puts("__VpadToAlign"+cvtToStr(alignr)
	     +"["+cvtToStr(padsize)+"];\n");
	alignr += padsize;
	m_declPadNum++;
    }
    alignr += size;
}

//----------------------------------------------------------------------
// Simple wrappers

void V3OutFormatter::printf (const char *fmt...) {
    char sbuff[5000];
    va_list ap;
    va_start(ap,fmt);
    vsprintf(sbuff,fmt,ap);
    va_end(ap);
    this->puts(sbuff);
}

//######################################################################
// V3OutFormatter: A class for printing to a file, with automatic indentation of C++ code.

V3OutFile::V3OutFile(const string& filename)
    : V3OutFormatter(filename, false) {
    if ((m_fp = V3File::new_fopen_w(filename.c_str())) == NULL) {
	v3fatal("Cannot write "<<filename);
    }
}

V3OutFile::~V3OutFile() {
    if (m_fp) fclose(m_fp);
    m_fp = NULL;
}
