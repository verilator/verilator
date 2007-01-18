// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <dirent.h>
#include <set>
#include <list>
#include <map>
#include <memory>

#include "V3Global.h"
#include "V3Options.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3PreShell.h"

#include "config_rev.h"

//######################################################################
// V3 Internal state

struct V3OptionsImp {
    // TYPES
    typedef std::map<string,set<string> > DirMap;	// Directory listing

    // STATE
    list<string>	m_allArgs;	// List of every argument encountered
    list<string>	m_incDirs;	// Include directories (ordered)
    set<string>		m_incDirSet;	// Include directories (for removing duplicates)
    set<string>		m_libExts;	// Library extensions
    DirMap		m_dirMap;	// Directory listing

    // ACCESSOR METHODS
    void addIncDir(const string& incdir) {
	if (m_incDirSet.find(incdir) == m_incDirSet.end()) {
	    m_incDirSet.insert(incdir);
	    m_incDirs.push_back(incdir);
	}
    }
    void addLibExt(const string& libext) {
	if (m_libExts.find(libext) == m_libExts.end()) {
	    m_libExts.insert(libext);
	}
    }
    V3OptionsImp() {}
};

void V3Options::addIncDir(const string& incdir) {
    m_impp->addIncDir(incdir);
}
void V3Options::addLibExt(const string& libext) {
    m_impp->addLibExt(libext);
}
void V3Options::addDefine(const string& defline) {
    // Split +define+foo=value into the appropriate parts and parse
    string def = defline;
    string value;
    string::size_type pos;
    if ( ((pos=defline.find("+")) != string::npos)
	 || ((pos=defline.find("=")) != string::npos)) {
	value = def.substr(pos+1);
	def.erase(pos);
    }
    V3PreShell::define(def,value);
}

void V3Options::addCppFile(const string& filename) {
    if (m_cppFiles.find(filename) == m_cppFiles.end()) {
	m_cppFiles.insert(filename);
    }
}
void V3Options::addLibraryFile(const string& filename) {
    if (m_libraryFiles.find(filename) == m_libraryFiles.end()) {
	m_libraryFiles.insert(filename);
    }
}
void V3Options::addArg(const string& arg) {
    m_impp->m_allArgs.push_back(arg);
}

string V3Options::allArgsString() {
    string out;
    for (list<string>::iterator it=m_impp->m_allArgs.begin(); it!=m_impp->m_allArgs.end(); ++it) {
	if (out != "") out += " ";
	out += *it;
    }
    return out;
}

//######################################################################
// File searching

string V3Options::filenameFromDirBase (const string& dir, const string& basename) {
    // Don't return ./{filename} because if filename was absolute, that makes it relative
    if (dir == ".") return basename;
    else return dir+"/"+basename;
}

string V3Options::filenameDir (const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind("/")) != string::npos) {
	return filename.substr(0,pos);
    } else {
	return ".";
    }
}

string V3Options::filenameNonDir (const string& filename) {
    string::size_type pos;
    if ((pos = filename.rfind("/")) != string::npos) {
	return filename.substr(pos+1);
    } else {
	return filename;
    }
}

string V3Options::filenameNonExt (const string& filename) {
    string base = filenameNonDir(filename);
    string::size_type pos;
    if ((pos = base.find(".")) != string::npos) {
	base.erase(pos);
    }
    return base;
}

bool V3Options::fileStatNormal(const string& filename) {
    struct stat	m_stat;		// Stat information
    int err = stat(filename.c_str(), &m_stat);
    if (err!=0) return false;
    if (S_ISDIR(m_stat.st_mode)) return false;
    return true;
}

string V3Options::fileExists (const string& filename) {
    // Surprisingly, for VCS and other simulators, this process
    // is quite slow; presumably because of re-reading each directory
    // many times.  So we read a whole dir at once and cache it

    string dir = filenameDir(filename);
    string basename = filenameNonDir(filename);

    V3OptionsImp::DirMap::iterator diriter = m_impp->m_dirMap.find(dir);
    if (diriter == m_impp->m_dirMap.end()) {
	// Read the listing
	m_impp->m_dirMap.insert(make_pair(dir, set<string>() ));
	diriter = m_impp->m_dirMap.find(dir);

	set<string>* setp = &(diriter->second);

	if (DIR* dirp = opendir(dir.c_str())) {
	    while (struct dirent* direntp = readdir(dirp)) {
		
		setp->insert(direntp->d_name);
	    }
	    closedir(dirp);
	}
    }
    // Find it
    set<string>* filesetp = &(diriter->second);
    set<string>::iterator fileiter = filesetp->find(basename);
    if (fileiter == filesetp->end()) {
	return "";  // Not found
    }
    // Check if it is a directory, ignore if so
    string filenameOut = filenameFromDirBase (dir, basename);
    if (!fileStatNormal(filenameOut)) return "";   // Directory
    return filenameOut;
}

string V3Options::filePath (FileLine* fl, const string& modname, const string& errmsg) {
    // Find a filename to read the specified module name,
    // using the incdir and libext's.
    // Return "" if not found.
    for (list<string>::iterator dirIter=m_impp->m_incDirs.begin(); dirIter!=m_impp->m_incDirs.end(); ++dirIter) {
	for (set<string>::iterator extIter=m_impp->m_libExts.begin(); extIter!=m_impp->m_libExts.end(); ++extIter) {
	    string fn = filenameFromDirBase(*dirIter,modname+*extIter);
	    string exists = fileExists(fn);
	    if (exists!="") {
		// Strip ./, it just looks ugly
		if (exists.substr(0,2)=="./") exists.erase(0,2);
		return exists;
	    }
	}
    }

    // Warn and return not found
    fl->v3error(errmsg+modname);
    static bool shown_notfound_msg = false;
    if (!shown_notfound_msg) {
	shown_notfound_msg = true;
	if (m_impp->m_incDirs.empty()) {
	    fl->v3error("This may be because there's no search path specified with -I<dir>."<<endl);
	} else {
	    fl->v3error("Looked in:"<<endl);
	    for (list<string>::iterator dirIter=m_impp->m_incDirs.begin(); dirIter!=m_impp->m_incDirs.end(); ++dirIter) {
		for (set<string>::iterator extIter=m_impp->m_libExts.begin(); extIter!=m_impp->m_libExts.end(); ++extIter) {
		    string fn = filenameFromDirBase(*dirIter,modname+*extIter);
		    fl->v3error("      "<<fn<<endl);
		}
	    }
	}
    }
    return "";
}

//######################################################################
// V3 Options accessors

string V3Options::version() {
    string ver = DTVERSION;
    ver += " rev"+cvtToStr(DTVERSION_rev);
#ifdef NEW_ORDERING
    ver += " (ord)";
#endif
    return ver;
}

//######################################################################
// V3 Options utilities

string V3Options::argString (int argc, char** argv) {
    // Return list of arguments as simple string
    string opts;
    for (int i=0; i<argc; i++)  {
	if (i!=0) opts += " ";
	opts += string(argv[i]);
    }
    return opts;
}

//######################################################################
// V3 Options Parsing

void V3Options::parseOpts (FileLine* fl, int argc, char** argv) {
    // Parse all options
    // Inital entry point from Verilator.cpp
    parseOptsList (fl, argc, argv);

    // Default certain options and error check
    // Detailed error, since this is what we often get when run with minimal arguments
    if (top()=="") {
	v3fatal("verilator: No Input Verilog file specified on command line, see verilator --help for more information\n");
    }

    // Default prefix to the filename
    if (prefix()=="") m_prefix = string("V")+filenameNonExt(top());
    if (modPrefix()=="") m_modPrefix = prefix();

    // Find files in makedir
    addIncDir(makeDir());
}

//======================================================================

bool V3Options::onoff(const char* sw, const char* arg, bool& flag) {
    // if sw==arg, then return true (found it), and flag=true
    // if sw=="-no-arg", then return true (found it), and flag=false
    // if sw=="-noarg", then return true (found it), and flag=false
    // else return false
    if (arg[0]!='-') v3fatalSrc("OnOff switches must have leading dash.\n");
    if (0==strcmp(sw,arg)) { flag=true; return true; }
    else if (0==strncmp(sw,"-no",3) && (0==strcmp(sw+3,arg+1))) { flag=false; return true; }
    else if (0==strncmp(sw,"-no-",4) && (0==strcmp(sw+4,arg+1))) { flag=false; return true; }
    return false;
}

void V3Options::parseOptsList(FileLine* fl, int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
    for (int i=0; i<argc; i++)  {
	addArg(argv[i]);	// -f's really should be inserted in the middle, but this is for debug
    }
#define shift { ++i; }
    for (int i=0; i<argc; )  {
	UINFO(9, " Option: "<<argv[i]<<endl);
	if (argv[i][0]=='+') {
	    char *sw = argv[i];
	    if ( !strncmp (sw, "+define+", 8)) {
		addDefine (string (sw+strlen("+define+")));
	    }
	    else if ( !strncmp (sw, "+incdir+", 8)) {
		addIncDir (string (sw+strlen("+incdir+")));
	    }
	    else if ( !strncmp (sw, "+libext+", 8)) {
		string exts = string(sw+strlen("+libext+"));
		string::size_type pos;
		while ((pos=exts.find("+")) != string::npos) {
		    addLibExt (exts.substr(0,pos));
		    exts = exts.substr(pos+1);
		}
		addLibExt (exts);
	    }
	    else if ( !strcmp (sw, "+librescan")) { // NOP
	    }
	    else {
		fl->v3fatal ("Invalid Option: "<<argv[i]);
	    }
	    shift;
	} // + options
	else if (argv[i][0]=='-') {
	    char *sw = argv[i];
	    bool flag = true;
	    // Allow gnu -- switches
	    if (sw[0]=='-' && sw[1]=='-') sw++;
	    // Switch tests
	    if ( !strcmp (sw, "-debug") ) {
		setDebugMode(3);
	    }
	    else if ( !strcmp (sw, "-debugi") ) {
		shift;
		setDebugMode(atoi(argv[i]));
	    }
	    else if ( !strcmp (sw, "-v") ) {
		shift;
		V3Options::addLibraryFile(argv[i]);
	    }
	    else if ( !strcmp (sw, "-version") ) {
		cout <<version();
		cout <<endl;
		exit(0);
	    }
	    else if ( !strcmp (sw, "-inline-mult") ) {
		shift;
		m_inlineMult = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-output-split") ) {
		shift;
		m_outputSplit = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-output-split-cfuncs") ) {
		shift;
		m_outputSplitCFuncs = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-trace-depth") ) {
		shift;
		m_traceDepth = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-unroll-count") ) { // Undocumented optimization tweak
		shift;
		m_unrollCount = atoi(argv[i]);
	    }
	    else if ( !strcmp (sw, "-unroll-stmts") ) {	// Undocumented optimization tweak
		shift;
		m_unrollStmts = atoi(argv[i]);
	    }
	    // Single switches
	    else if ( !strcmp (sw, "-E") )			{ m_preprocOnly = true; }
	    else if ( onoff   (sw, "-MMD", flag/*ref*/) )	{ m_makeDepend = flag; }
	    else if ( onoff   (sw, "-MP", flag/*ref*/) )	{ m_makePhony = flag; }
	    else if ( onoff   (sw, "-assert", flag/*ref*/) )	{ m_assert = flag; m_psl = flag; }
	    else if ( !strcmp (sw, "-cc") )			{ m_outFormatOk = true; m_systemC = false; m_systemPerl = false; }
	    else if ( onoff   (sw, "-coverage", flag/*ref*/) )	{ coverage(flag); }
	    else if ( onoff   (sw, "-coverage-line", flag/*ref*/) ){ m_coverageLine = flag; }
	    else if ( onoff   (sw, "-coverage-user", flag/*ref*/) ){ m_coverageUser = flag; }
	    else if ( onoff   (sw, "-covsp", flag/*ref*/) )	{ }  // TBD
	    else if ( onoff   (sw, "-debug-check", flag/*ref*/) ){ m_debugCheck = flag; }
	    else if ( onoff   (sw, "-dump-tree", flag/*ref*/) )	{ m_dumpTree = flag; }
	    else if ( onoff   (sw, "-exe", flag/*ref*/) )	{ m_exe = flag; }
	    else if ( onoff   (sw, "-ignc", flag/*ref*/) )	{ m_ignc = flag; }
	    else if ( onoff   (sw, "-inhibit-sim", flag/*ref*/)){ m_inhibitSim = flag; }
	    else if ( onoff   (sw, "-l2name", flag/*ref*/) )	{ m_l2Name = flag; }
	    else if ( onoff   (sw, "-pins64", flag/*ref*/) )	{ m_pins64 = flag; }
	    else if ( !strcmp (sw, "-private") )		{ m_public = false; }
	    else if ( onoff   (sw, "-profile-cfuncs", flag/*ref*/) )	{ m_profileCFuncs = flag; }
	    else if ( onoff   (sw, "-psl", flag/*ref*/) )		{ m_psl = flag; }
	    else if ( onoff   (sw, "-public", flag/*ref*/) )		{ m_public = flag; }
	    else if ( !strcmp (sw, "-sc") )				{ m_outFormatOk = true; m_systemC = true; m_systemPerl = false; }
	    else if ( !strcmp (sw, "-sp") )				{ m_outFormatOk = true; m_systemC = true; m_systemPerl = true; }
	    else if ( onoff   (sw, "-skip-identical", flag/*ref*/) )	{ m_skipIdentical = flag; }
	    else if ( onoff   (sw, "-stats", flag/*ref*/) )		{ m_stats = flag; }
	    else if ( onoff   (sw, "-trace", flag/*ref*/) )		{ m_trace = flag; }
	    else if ( onoff   (sw, "-trace-dups", flag/*ref*/) )	{ m_traceDups = flag; }
	    else if ( onoff   (sw, "-underline-zero", flag/*ref*/) )	{ m_underlineZero = flag; }
	    // Optimization
	    else if ( !strncmp (sw, "-O", 2) ) {
		for (char* cp=sw+strlen("-O"); *cp; cp++) {
		    flag = isupper(*cp);
		    switch (tolower(*cp)) {
		    case '0': optimize(0); break; // 0=all off
		    case '1': optimize(1); break; // 1=all on
		    case '2': optimize(2); break; // 2=not used
		    case '3': optimize(3); break; // 3=high
		    case 'a': m_oTable = flag; break;
		    case 'b': m_oCombine = flag; break;
		    case 'c': m_oConst = flag; break;
		    case 'e': m_oCase = flag; break;
		    case 'g': m_oGate = flag; break;
		    case 'i': m_oInline = flag; break;
		    case 'k': m_oSubstConst = flag; break;
		    case 'l': m_oLife = flag; break;
		    case 'p': m_public = !flag; break;  //With -Op so flag=0, we want public on so few optimizations done
		    case 'r': m_oReorder = flag; break;
		    case 's': m_oSplit = flag; break;
		    case 't': m_oLifePost = flag; break;
		    case 'u': m_oSubst = flag; break;
		    case 'x': m_oExpand = flag; break;
		    case 'y': m_oAcycSimp = flag; break;
		    case 'z': m_oLocalize = flag; break;
		    default:  break; // No error, just ignore
		    }
		}
	    }
	    // Parameterized switches
	    else if ( !strncmp (sw, "-D", 2)) {
		addDefine (string (sw+strlen("-D")));
	    }
	    else if ( !strncmp (sw, "-I", 2)) {
		addIncDir (string (sw+strlen("-I")));
	    }
	    else if ( !strcmp (sw, "-Mdir") && (i+1)<argc ) {
		shift; m_makeDir = argv[i];
		addIncDir (string (m_makeDir));	 // Need to find generated files there too
	    }
	    else if ( !strncmp (sw, "-U", 2)) {
		V3PreShell::undef (string (sw+strlen("-U")));
	    }
	    else if ( !strncmp (sw, "-Wno-",5) )	{
		string msg = sw+strlen("-Wno-");
		if (!(FileLine::defaultFileLine().warnOff(msg, true))) {
		    fl->v3fatal("Unknown warning disabled: "<<sw);
		}
	    }
	    else if ( !strncmp (sw, "-Werror-",strlen("-Werror-")) )	{
		string msg = sw+strlen("-Werror-");
		V3ErrorCode code (msg.c_str());
		if (code == V3ErrorCode::ERROR) {
		    fl->v3fatal("Unknown warning specified: "<<sw);
		} else {
		    V3Error::pretendError(code, true);
		}
	    }
	    else if ( !strcmp (sw, "-x-assign") && (i+1)<argc) {
		shift;
		if (!strcmp (argv[i], "0")) { m_xAssign="0"; }
		else if (!strcmp (argv[i], "1")) { m_xAssign="1"; }
		else if (!strcmp (argv[i], "unique")) { m_xAssign="unique"; }
		else {
		    fl->v3fatal("Unknown setting for -x-assign: "<<sw);
		}
	    }
	    else if ( !strcmp (sw, "-bin") && (i+1)<argc ) {
		shift; m_bin = argv[i];
	    }
	    else if ( !strcmp (sw, "-f") && (i+1)<argc ) {
		shift;
		parseOptsFile(fl, argv[i]);
	    }
	    else if ( !strcmp (sw, "-gdb") && (i+1)<argc ) {
		shift; // Used only in perl shell
	    }
	    else if ( !strcmp (sw, "-mod-prefix") && (i+1)<argc ) {
		shift; m_modPrefix = argv[i];
	    }
	    else if ( !strcmp (sw, "-prefix") && (i+1)<argc ) {
		shift; m_prefix = argv[i];
		if (m_modPrefix=="") m_modPrefix = m_prefix;
	    }
	    else if ( !strcmp (sw, "-y")) {
		shift; addIncDir (string (argv[i]));
	    }
	    else {
		fl->v3fatal ("Invalid Option: "<<argv[i]);
	    }
	    shift;
	} // - options
	else {
	    // Filename
	    string filename = argv[i];
	    if (filename.find(".cpp") != string::npos
		|| filename.find(".cxx") != string::npos
		|| filename.find(".cc") != string::npos
		|| filename.find(".sp") != string::npos) {
		V3Options::addCppFile(argv[i]);
	    } else {
		if (m_top!="") fl->v3fatal ("Top filename specified twice: "<<m_top<<" and "<<filename);
		m_top = filename;
	    }
	    shift;
	}
    }
#undef shift
}

//======================================================================

void V3Options::parseOptsFile(FileLine* fl, const string& filename) {
    // Read the specified -f filename and process as arguments
    UINFO(1,"Reading Options File "<<filename<<endl);

    const auto_ptr<ifstream> ifp (V3File::new_ifstream(filename));
    if (ifp->fail()) {
	fl->v3error("Cannot open -f command file: "+filename);
	return;
    }

    string whole_file;
    string::size_type pos;
    while (!ifp->eof()) {
	string line;
	getline(*ifp, line);
	// Strip simple comments
	if ((pos=line.find("//")) != string::npos) {
	    line.erase(pos);
	}
	whole_file += line + " ";
    }
    whole_file += "\n";  // So string match below is simplified

    fl = new FileLine(filename, 0);

    // Split into argument list and process
    // Note we don't respect quotes.  It seems most simulators dont.
    // Woez those that expect it; we'll at least complain.
    if ((pos=whole_file.find("\"")) != string::npos) {
	fl->v3error("Double quotes in -f files cause unspecified behavior.");
    }

    // Strip off arguments and parse into words
    vector<string> args;
    string::size_type startpos = 0;
    while (startpos < whole_file.length()) {
	while (isspace(whole_file[startpos])) startpos++;
	string::size_type endpos = startpos;
	while (endpos < whole_file.length() && !isspace(whole_file[endpos])) endpos++;
	if (startpos != endpos) {
	    string arg (whole_file, startpos, endpos-startpos);
	    args.reserve(args.size()+1);
	    args.push_back(arg);
	}
	startpos = endpos;
    }

    // Convert to argv style arg list and parse them
    char* argv [args.size()+1];
    for (unsigned i=0; i<args.size(); i++) {
	argv[i] = (char*)args[i].c_str();
    }
    parseOptsList(fl, args.size(), argv);
}

//======================================================================

V3Options::V3Options() {
    m_impp = new V3OptionsImp;

    m_coverageLine = false;
    m_coverageUser = false;
    m_debugCheck = false;
    m_dumpTree = false;
    m_exe = false;
    m_ignc = false;
    m_l2Name = true;
    m_makeDepend = true;
    m_makePhony = false;
    m_outFormatOk = false;
    m_pins64 = false;
    m_profileCFuncs = false;
    m_preprocOnly = false;
    m_psl = false;
    m_public = false;
    m_skipIdentical = true;
    m_stats = false;
    m_systemC = false;
    m_systemPerl = false;
    m_trace = false;
    m_traceDups = false;
    m_underlineZero = false;

    m_inlineMult = 2000;
    m_outputSplit = 0;
    m_outputSplitCFuncs = 0;
    m_traceDepth = 0;
    m_unrollCount = 64;
    m_unrollStmts = 20;

    m_makeDir = "obj_dir";
    m_bin = "";
    m_flags = "";
    m_xAssign = "unique";

    optimize(true);
    // Default +libext+
    addLibExt("");  // So include "filename.v" will find the same file
    addLibExt(".v");
    // Default -I
    addIncDir(".");	// Looks better then {long_cwd_path}/...
}

V3Options::~V3Options() {
    delete m_impp; m_impp=NULL;
}

void V3Options::setDebugMode(int level) {
    V3Error::debugDefault(level);
    m_dumpTree = true;
    m_stats = true;
    m_debugCheck = true;
    cout << "Starting "<<version()<<endl;
}

void V3Options::optimize(int level) {
    // Set all optimizations to on/off
    bool flag = level > 0;
    m_oAcycSimp = flag;
    m_oCase = flag;
    m_oCombine = flag;
    m_oConst = flag;
    m_oExpand = flag;
    m_oGate = flag;
    m_oInline = flag;
    m_oLife = flag;
    m_oLifePost = flag;
    m_oLocalize = flag;
    m_oReorder = flag;
    m_oSplit = flag;
    m_oSubst = flag;
    m_oSubstConst = flag;
    m_oTable = flag;
    // And set specific optimization levels
    if (level >= 3) {
	m_inlineMult = -1;	// Maximum inlining
    }
}
