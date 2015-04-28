// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: File stream wrapper that understands indentation
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdarg>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <cerrno>
#include <fcntl.h>
#include <iomanip>
#include <memory>
#include <map>

#if defined(__unix__) || defined(__unix) || (defined(__APPLE__) && defined(__MACH__))
# define INFILTER_PIPE  // Allow pipe filtering.  Needs fork()
#endif

#ifdef INFILTER_PIPE
# include <sys/wait.h>
#endif

#include "V3Global.h"
#include "V3File.h"
#include "V3Os.h"
#include "V3PreShell.h"
#include "V3Ast.h"

// If change this code, run a test with the below size set very small
//#define INFILTER_IPC_BUFSIZ 16
#define INFILTER_IPC_BUFSIZ 64*1024  // For debug, try this as a small number
#define INFILTER_CACHE_MAX  64*1024  // Maximum bytes to cache if same file read twice

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
	ino_t ino() const { return m_stat.st_ino; }
	time_t mtime() const { return m_stat.st_mtime; }
	void loadStats() {
	    if (!m_stat.st_mtime) {
		string fn = filename();
		int err = stat(fn.c_str(), &m_stat);
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
    const VL_UNIQUE_PTR<ofstream> ofp (V3File::new_ofstream(filename));
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
    const VL_UNIQUE_PTR<ofstream> ofp (V3File::new_ofstream(filename));
    if (ofp->fail()) v3fatalSrc("Can't write "<<filename);

    string cmdline = stripQuotes(cmdlineIn);
    *ofp<<"# DESCR"<<"IPTION: Verilator output: Timestamp data for --skip-identical.  Delete at will."<<endl;
    *ofp<<"C \""<<cmdline<<"\""<<endl;

    for (set<DependFile>::iterator iter=m_filenameList.begin();
	 iter!=m_filenameList.end(); ++iter) {
	// Read stats of files we create after we're done making them (execpt for this file, of course)
	DependFile* dfp = (DependFile*)&(*iter);
	V3Options::fileNfsFlush(dfp->filename());
	dfp->loadStats();
	off_t showSize = iter->size();
	ino_t showIno = iter->ino();
	if (dfp->filename() == filename) { showSize=0; showIno=0; }  // We're writing it, so need to ignore it

	*ofp<<(iter->target()?"T":"S")<<" ";
	*ofp<<" "<<setw(8)<<showSize;
	*ofp<<" "<<setw(8)<<showIno;
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
	ino_t  chkIno;   *ifp>>chkIno;
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
		  && chkStat.st_ino == chkIno
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
	V3Os::createDir(v3Global.opt.makeDir());
    }
}

//######################################################################
// V3InFilterImp

class V3InFilterImp {
    typedef map<string,string> FileContentsMap;
    typedef V3InFilter::StrList StrList;

    FileContentsMap	m_contentsMap;	// Cache of file contents
    bool		m_readEof;	// Received EOF on read
#ifdef INFILTER_PIPE
    pid_t		m_pid;		// fork() process id
#else
    int			m_pid;		// fork() process id - always zero as disabled
#endif
    bool		m_pidExited;
    int			m_pidStatus;
    int			m_writeFd;	// File descriptor TO filter
    int			m_readFd;	// File descriptor FROM filter

private:
    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    bool readContents(const string& filename, StrList& outl) {
	if (m_pid) return readContentsFilter(filename,outl);
	else return readContentsFile(filename,outl);
    }
    bool readContentsFile(const string& filename, StrList& outl) {
	int fd = open (filename.c_str(), O_RDONLY);
	if (fd<0) return false;
	m_readEof = false;
	readBlocks(fd, -1, outl);
	close(fd);
	return true;
    }
    bool readContentsFilter(const string& filename, StrList& outl) {
	if (filename!="" || outl.empty()) {}  // Prevent unused
#ifdef INFILTER_PIPE
	writeFilter("read \""+filename+"\"\n");
	string line = readFilterLine();
	if (line.find("Content-Length") != string::npos) {
	    int len = 0;
	    sscanf(line.c_str(), "Content-Length: %d\n", &len);
	    readBlocks(m_readFd, len, outl);
	    return true;
	} else {
	    if (line!="") v3error("--pipe-filter protocol error, unexpected: "<<line);
	    return false;
	}
#else
	v3fatalSrc("--pipe-filter not implemented on this platform");
	return false;
#endif
    }

    // cppcheck-suppress functionConst
    void checkFilter(bool hang) {
#ifdef INFILTER_PIPE
	if (!m_pidExited && waitpid(m_pid, &m_pidStatus, hang?0:WNOHANG)) {
	    UINFO(1,"--pipe-filter: Exited, status "<<m_pidStatus<<" exit="<<WEXITSTATUS(m_pidStatus)<<" err"<<strerror(errno)<<endl);
	    m_readEof = true;
	    m_pidExited = true;
	}
#endif
    }

    string readBlocks(int fd, int size, StrList& outl) {
	string out;
	char buf[INFILTER_IPC_BUFSIZ];
	ssize_t sizegot = 0;
	while (!m_readEof && (size<0 || size>sizegot)) {
	    ssize_t todo = INFILTER_IPC_BUFSIZ;
	    if (size>0 && size<todo) todo = size;
	    errno = 0;
	    ssize_t got = read (fd, buf, todo);
	    //UINFO(9,"RD GOT g "<< got<<" e "<<errno<<" "<<strerror(errno)<<endl);  usleep(50*1000);
	    if (got>0) {
		outl.push_back(string(buf, got));
		sizegot += got;
	    }
	    else if (errno == EINTR || errno == EAGAIN
#ifdef EWOULDBLOCK
		     || errno == EWOULDBLOCK
#endif
		) {
		// cppcheck-suppress obsoleteFunctionsusleep
		checkFilter(false); usleep(1000); continue;
	    } else { m_readEof = true; break; }
	}
	return out;
    }
    string readFilterLine() {
	// Slow, but we don't need it much
	UINFO(9,"readFilterLine\n");
	string line;
	while (!m_readEof) {
	    StrList outl;
	    readBlocks(m_readFd, 1, outl);
	    string onechar = listString(outl);
	    line += onechar;
	    if (onechar == "\n") {
		if (line == "\n") { line=""; continue; }
		else break;
	    }
	}
	UINFO(6,"filter-line-in: "<<line);
	return line;
    }
    void writeFilter(const string& out) {
	if (debug()>=6) { UINFO(6,"filter-out: "<<out); if (out[out.length()-1]!='\n') cout<<endl; }
	if (!m_pid) { v3error("--pipe-filter: write to closed file\n"); m_readEof = true; stop(); }
	unsigned offset = 0;
	while (!m_readEof && out.length()>offset) {
	    errno = 0;
	    int got = write (m_writeFd, (out.c_str())+offset, out.length()-offset);
	    //UINFO(9,"WR GOT g "<< got<<" e "<<errno<<" "<<strerror(errno)<<endl);  usleep(50*1000);
	    if (got>0) offset += got;
	    else if (errno == EINTR || errno == EAGAIN
#ifdef EWOULDBLOCK
		     || errno == EWOULDBLOCK
#endif
		) {
		// cppcheck-suppress obsoleteFunctionsusleep
		checkFilter(false); usleep(1000); continue;
	    }
	    else break;
	}
    }

    // Start the filter
    void start(const string& command) {
	if (command=="") {
	    m_pid = 0;  // Disabled
	} else {
	    startFilter(command);
	}
    }
    void startFilter(const string& command) {
	if (command=="") {} // Prevent Unused
#ifdef INFILTER_PIPE
	int fd_stdin[2], fd_stdout[2];
	static const int P_RD = 0;
	static const int P_WR = 1;

	if (pipe(fd_stdin) != 0 || pipe(fd_stdout) != 0) {
	    v3fatal("--pipe-filter: Can't pipe: "<<strerror(errno));
	}
	if (fd_stdin[P_RD]<=2 || fd_stdin[P_WR]<=2
	    || fd_stdout[P_RD]<=2 || fd_stdout[P_WR]<=2) {
	    // We'd have to rearrange all of the FD usages in this case.
	    // Too unlikely; verilator isn't a daemon.
	    v3fatal("--pipe-filter: stdin/stdout closed before pipe opened\n");
	}

	UINFO(1,"--pipe-filter: /bin/sh -c "<<command<<endl);

	pid_t pid = fork();
	if (pid < 0) v3fatal("--pipe-filter: fork failed: "<<strerror(errno));
	if (pid == 0) {  // Child
	    UINFO(6,"In child\n");
	    close(fd_stdin[P_WR]);
	    dup2(fd_stdin[P_RD], 0);
	    close(fd_stdout[P_RD]);
	    dup2(fd_stdout[P_WR], 1);
	    // And stderr comes from parent

	    execl("/bin/sh", "sh", "-c", command.c_str(), (char*)NULL);
	    // Don't use v3fatal, we don't share the common structures any more
	    fprintf(stderr,"--pipe-filter: exec failed: %s\n",strerror(errno));
	    _exit(10);
	}
	else {  // Parent
	    UINFO(6,"In parent, child pid "<<pid
		  <<" stdin "<<fd_stdin[P_WR]<<"->"<<fd_stdin[P_RD]
		  <<" stdout "<<fd_stdout[P_WR]<<"->"<<fd_stdout[P_RD]<<endl);
	    m_pid = pid;
	    m_pidExited = false;
	    m_pidStatus = 0;
	    m_writeFd = fd_stdin[P_WR];
	    m_readFd = fd_stdout[P_RD];
	    m_readEof = false;

	    close(fd_stdin[P_RD]);
	    close(fd_stdout[P_WR]);

	    int flags = fcntl(m_readFd,F_GETFL,0);
	    fcntl(m_readFd, F_SETFL, flags | O_NONBLOCK);

	    flags = fcntl(m_writeFd,F_GETFL,0);
	    fcntl(m_writeFd, F_SETFL, flags | O_NONBLOCK);
	}
	UINFO(6,"startFilter complete\n");
#else
	v3fatalSrc("--pipe-filter not implemented on this platform");
#endif
    }

    void stop() {
	if (m_pid) stopFilter();
    }
    void stopFilter() {
	UINFO(6,"Stopping filter process\n");
#ifdef INFILTER_PIPE
	close(m_writeFd);
	checkFilter(true);
	if (!WIFEXITED(m_pidStatus) || WEXITSTATUS(m_pidStatus)!=0) {
	    v3fatal("--pipe-filter returned bad status");
	}
	m_pid = 0;
	close(m_readFd);
	UINFO(6,"Closed\n");
#else
	v3fatalSrc("--pipe-filter not implemented on this platform");
#endif
    }

protected:
    friend class V3InFilter;
    // Read file contents and return it
    bool readWholefile(const string& filename, StrList& outl) {
	FileContentsMap::iterator it = m_contentsMap.find(filename);
	if (it != m_contentsMap.end()) {
	    outl.push_back(it->second);
	    return true;
	}
	if (!readContents(filename, outl)) return false;
	if (listSize(outl) < INFILTER_CACHE_MAX) {
	    // Cache small files (only to save space)
	    // It's quite common to `include "timescale" thousands of times
	    // This isn't so important if it's just a open(), but filtering can be slow
	    m_contentsMap.insert(make_pair(filename,listString(outl)));
	}
	return true;
    }
    size_t listSize(StrList& sl) {
	size_t out = 0;
	for (StrList::iterator it=sl.begin(); it!=sl.end(); ++it) {
	    out += it->length();
	}
	return out;
    }
    string listString(StrList& sl) {
	string out;
	for (StrList::iterator it=sl.begin(); it!=sl.end(); ++it) {
	    out += *it;
	}
	return out;
    }
    // CONSTRUCTORS
    V3InFilterImp(const string& command) {
	m_readEof = false;
	m_pid = 0;
	m_pidExited = false;
	m_pidStatus = 0;
	m_writeFd = 0;
	m_readFd = 0;
	start(command);
    }
    ~V3InFilterImp() { stop(); }
};

//######################################################################
// V3InFilter
// Just dispatch to the implementation

V3InFilter::V3InFilter(const string& command) { m_impp = new V3InFilterImp(command); }
V3InFilter::~V3InFilter() { if (m_impp) delete m_impp; m_impp=NULL; }

bool V3InFilter::readWholefile(const string& filename, V3InFilter::StrList& outl) {
    if (!m_impp) v3fatalSrc("readWholefile on invalid filter");
    return m_impp->readWholefile(filename, outl);
}

//######################################################################
// V3OutFormatter: A class for printing to a file, with automatic indentation of C++ code.

V3OutFormatter::V3OutFormatter(const string& filename, V3OutFormatter::Language lang)
    : m_filename(filename), m_lang(lang)
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
    if (m_lang!=LA_VERILOG) {  // verilogPrefixedTree doesn't want tabs
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
	case '<':
	    if (m_lang==LA_XML) {
		if (cp[1] == '/') levels-=INDBLK;
	    }
	    break;
	case 'e':
	    if (m_lang==LA_VERILOG && tokenEnd(cp)) {
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
	case '}':
	    indentDec();
	    break;
	case '(':
	    indentInc();
	    m_parenVec.push(m_column);
	    break;
	case ')':
	    if (!m_parenVec.empty()) m_parenVec.pop();
	    indentDec();
	    break;
	case '<':
	    if (m_lang==LA_XML) {
		if (cp[1] == '/') {} // Zero as the > will result in net decrease by one
		else if (cp[1] == '!' || cp[1] == '?') { indentInc(); } // net same indent
		else { indentInc(); indentInc(); }  // net increase by one
	    }
	    break;
	case '>':
	    if (m_lang==LA_XML) {
		indentDec();
		if (cp>strg && cp[-1]=='/') indentDec();   // < ..... /> stays same level
	    }
	    break;
	case 'b':
	    if (wordstart && m_lang==LA_VERILOG && tokenStart(cp,"begin")) {
		indentInc();
	    }
	    wordstart = false;
	    break;
	case 'c':
	    if (wordstart && m_lang==LA_VERILOG
		&& (tokenStart(cp,"case")
		    || tokenStart(cp,"casex")
		    || tokenStart(cp,"casez"))) {
		indentInc();
	    }
	    wordstart = false;
	    break;
	case 'e':
	    if (wordstart && m_lang==LA_VERILOG && tokenEnd(cp)) {
		indentDec();
	    }
	    wordstart = false;
	    break;
	case 'm':
	    if (wordstart && m_lang==LA_VERILOG && tokenStart(cp,"module")) {
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
    string quoted = V3Number::quoteNameControls(strg);
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

V3OutFile::V3OutFile(const string& filename, V3OutFormatter::Language lang)
    : V3OutFormatter(filename, lang) {
    if ((m_fp = V3File::new_fopen_w(filename.c_str())) == NULL) {
	v3fatal("Cannot write "<<filename);
    }
}

V3OutFile::~V3OutFile() {
    if (m_fp) fclose(m_fp);
    m_fp = NULL;
}
