// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2015 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
//=============================================================================
///
/// \file
/// \brief C++ Tracing in VCD Format
///
//=============================================================================
// SPDIFF_OFF

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <cerrno>
#include <ctime>
#include <algorithm>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

// SPDIFF_ON

#ifndef O_LARGEFILE // For example on WIN32
# define O_LARGEFILE 0
#endif
#ifndef O_NONBLOCK
# define O_NONBLOCK 0
#endif

//=============================================================================
// Global

vector<VerilatedVcd*>	VerilatedVcd::s_vcdVecp;	///< List of all created traces

//=============================================================================
// VerilatedVcdCallInfo
/// Internal callback routines for each module being traced.
////
/// Each module that wishes to be traced registers a set of
/// callbacks stored in this class.  When the trace file is being
/// constructed, this class provides the callback routines to be executed.

class VerilatedVcdCallInfo {
protected:
    friend class VerilatedVcd;
    VerilatedVcdCallback_t	m_initcb;	///< Initialization Callback function
    VerilatedVcdCallback_t	m_fullcb;	///< Full Dumping Callback function
    VerilatedVcdCallback_t	m_changecb;	///< Incremental Dumping Callback function
    void*		m_userthis;	///< Fake "this" for caller
    vluint32_t		m_code;		///< Starting code number
    // CREATORS
    VerilatedVcdCallInfo (VerilatedVcdCallback_t icb, VerilatedVcdCallback_t fcb,
			  VerilatedVcdCallback_t changecb,
			  void* ut, vluint32_t code)
	: m_initcb(icb), m_fullcb(fcb), m_changecb(changecb), m_userthis(ut), m_code(code) {};
};

//=============================================================================
//=============================================================================
//=============================================================================
// VerilatedVcdFile

bool VerilatedVcdFile::open(const string& name) {
    m_fd = ::open(name.c_str(), O_CREAT|O_WRONLY|O_TRUNC|O_LARGEFILE|O_NONBLOCK, 0666);
    return (m_fd>=0);
}

void VerilatedVcdFile::close() {
    ::close(m_fd);
}

ssize_t VerilatedVcdFile::write(const char* bufp, ssize_t len) {
    return ::write(m_fd, bufp, len);
}

//=============================================================================
//=============================================================================
//=============================================================================
// Opening/Closing

VerilatedVcd::VerilatedVcd(VerilatedVcdFile* filep)
    : m_isOpen(false), m_rolloverMB(0), m_modDepth(0), m_nextCode(1) {
    // Not in header to avoid link issue if header is included without this .cpp file
    m_fileNewed = (filep == NULL);
    m_filep = m_fileNewed ? new VerilatedVcdFile : filep;
    m_namemapp = NULL;
    m_timeRes = m_timeUnit = 1e-9;
    m_timeLastDump = 0;
    m_sigs_oldvalp = NULL;
    m_evcd = false;
    m_scopeEscape = '.';  // Backward compatibility
    m_fullDump = true;
    m_wrChunkSize = 8*1024;
    m_wrBufp = new char [m_wrChunkSize*8];
    m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
    m_writep = m_wrBufp;
    m_wroteBytes = 0;
}

void VerilatedVcd::open (const char* filename) {
    if (isOpen()) return;

    // Set member variables
    m_filename = filename;
    s_vcdVecp.push_back(this);

    // SPDIFF_OFF
    // Set callback so an early exit will flush us
    Verilated::flushCb(&flush_all);

    // SPDIFF_ON
    openNext (m_rolloverMB!=0);
    if (!isOpen()) return;

    dumpHeader();

    // Allocate space now we know the number of codes
    if (!m_sigs_oldvalp) {
	m_sigs_oldvalp = new vluint32_t [m_nextCode+10];
    }

    if (m_rolloverMB) {
	openNext(true);
	if (!isOpen()) return;
    }
}

void VerilatedVcd::openNext (bool incFilename) {
    // Open next filename in concat sequence, mangle filename if
    // incFilename is true.
    closePrev(); // Close existing
    if (incFilename) {
	// Find _0000.{ext} in filename
	string name = m_filename;
	size_t pos=name.rfind(".");
	if (pos>8 && 0==strncmp("_cat",name.c_str()+pos-8,4)
	    && isdigit(name.c_str()[pos-4])
	    && isdigit(name.c_str()[pos-3])
	    && isdigit(name.c_str()[pos-2])
	    && isdigit(name.c_str()[pos-1])) {
	    // Increment code.
	    if ((++(name[pos-1])) > '9') {
		name[pos-1] = '0';
		if ((++(name[pos-2])) > '9') {
		    name[pos-2] = '0';
		    if ((++(name[pos-3])) > '9') {
			name[pos-3] = '0';
			if ((++(name[pos-4])) > '9') {
			    name[pos-4] = '0';
			}}}}
	} else {
	    // Append _cat0000
	    name.insert(pos,"_cat0000");
	}
	m_filename = name;
    }
    if (m_filename[0]=='|') {
	assert(0);	// Not supported yet.
    } else {
	// cppcheck-suppress duplicateExpression
	if (!m_filep->open(m_filename)) {
	    // User code can check isOpen()
	    m_isOpen = false;
	    return;
	}
    }
    m_isOpen = true;
    m_fullDump = true;	// First dump must be full
    m_wroteBytes = 0;
}

void VerilatedVcd::makeNameMap() {
    // Take signal information from each module and build m_namemapp
    deleteNameMap();
    m_nextCode = 1;
    m_namemapp = new NameMap;
    for (vluint32_t ent = 0; ent< m_callbacks.size(); ent++) {
	VerilatedVcdCallInfo *cip = m_callbacks[ent];
	cip->m_code = nextCode();
	(cip->m_initcb) (this, cip->m_userthis, cip->m_code);
    }

    // Though not speced, it's illegal to generate a vcd with signals
    // not under any module - it crashes at least two viewers.
    // If no scope was specified, prefix everything with a "top"
    // This comes from user instantiations with no name - IE Vtop("").
    bool nullScope = false;
    for (NameMap::iterator it=m_namemapp->begin(); it!=m_namemapp->end(); ++it) {
	const string& hiername = it->first;
	if (hiername.size() >= 1 && hiername[0] == '\t') nullScope=true;
    }
    if (nullScope) {
	NameMap* newmapp = new NameMap;
	for (NameMap::iterator it=m_namemapp->begin(); it!=m_namemapp->end(); ++it) {
	    const string& hiername = it->first;
	    const string& decl     = it->second;
	    string newname = string("top");
	    if (hiername[0] != '\t') newname += ' ';
	    newname += hiername;
	    newmapp->insert(make_pair(newname,decl));
	}
	deleteNameMap();
	m_namemapp = newmapp;
    }
}

void VerilatedVcd::deleteNameMap() {
    if (m_namemapp) { delete m_namemapp; m_namemapp=NULL; }
}

VerilatedVcd::~VerilatedVcd() {
    close();
    if (m_wrBufp) { delete[] m_wrBufp; m_wrBufp=NULL; }
    if (m_sigs_oldvalp) { delete[] m_sigs_oldvalp; m_sigs_oldvalp=NULL; }
    deleteNameMap();
    if (m_filep && m_fileNewed) { delete m_filep; m_filep = NULL; }
    // Remove from list of traces
    vector<VerilatedVcd*>::iterator pos = find(s_vcdVecp.begin(), s_vcdVecp.end(), this);
    if (pos != s_vcdVecp.end()) { s_vcdVecp.erase(pos); }
}

void VerilatedVcd::closePrev () {
    if (!isOpen()) return;

    bufferFlush();
    m_isOpen = false;
    m_filep->close();
}

void VerilatedVcd::closeErr () {
    // Close due to an error.  We might abort before even getting here,
    // depending on the definition of vl_fatal.
    if (!isOpen()) return;

    // No buffer flush, just fclose
    m_isOpen = false;
    m_filep->close();  // May get error, just ignore it
}

void VerilatedVcd::close() {
    if (!isOpen()) return;
    if (m_evcd) {
	printStr("$vcdclose ");
	printTime(m_timeLastDump);
	printStr(" $end\n");
    }
    closePrev();
}

void VerilatedVcd::printStr (const char* str) {
    // Not fast...
    while (*str) {
	*m_writep++ = *str++;
	bufferCheck();
    }
}

void VerilatedVcd::printQuad (vluint64_t n) {
    char buf [100];
    sprintf(buf,"%" VL_PRI64 "u", n);
    printStr(buf);
}

void VerilatedVcd::printTime (vluint64_t timeui) {
    // VCD file format specification does not allow non-integers for timestamps
    // Dinotrace doesn't mind, but Cadence vvision seems to choke
    if (VL_UNLIKELY(timeui < m_timeLastDump)) {
	timeui = m_timeLastDump;
	static bool backTime = false;
	if (!backTime) {
	    backTime = true;
	    VL_PRINTF("VCD time is moving backwards, wave file may be incorrect.\n");
	}
    }
    m_timeLastDump = timeui;
    printQuad(timeui);
}

void VerilatedVcd::bufferResize(vluint64_t minsize) {
    // minsize is size of largest write.  We buffer at least 8 times as much data,
    // writing when we are 3/4 full (with thus 2*minsize remaining free)
    if (VL_UNLIKELY(minsize > m_wrChunkSize)) {
	char* oldbufp = m_wrBufp;
	m_wrChunkSize = minsize*2;
	m_wrBufp = new char [m_wrChunkSize * 8];
	memcpy(m_wrBufp, oldbufp, m_writep - oldbufp);
        m_writep = m_wrBufp + (m_writep - oldbufp);
	m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
	delete oldbufp; oldbufp=NULL;
    }
}

void VerilatedVcd::bufferFlush () {
    // We add output data to m_writep.
    // When it gets nearly full we dump it using this routine which calls write()
    // This is much faster than using buffered I/O
    if (VL_UNLIKELY(!isOpen())) return;
    char* wp = m_wrBufp;
    while (1) {
	ssize_t remaining = (m_writep - wp);
	if (remaining==0) break;
	errno = 0;
	ssize_t got = m_filep->write(wp, remaining);
	if (got>0) {
	    wp += got;
	    m_wroteBytes += got;
	} else if (got < 0) {
	    if (errno != EAGAIN && errno != EINTR) {
		// write failed, presume error (perhaps out of disk space)
		string msg = (string)"VerilatedVcd::bufferFlush: "+strerror(errno);
		vl_fatal("",0,"",msg.c_str());
		closeErr();
		break;
	    }
	}
    }

    // Reset buffer
    m_writep = m_wrBufp;
}

//=============================================================================
// Simple methods

void VerilatedVcd::set_time_unit (const char* unitp) {
    //cout<<" set_time_unit ("<<unitp<<") == "<<timescaleToDouble(unitp)<<" == "<<doubleToTimescale(timescaleToDouble(unitp))<<endl;
    m_timeUnit = timescaleToDouble(unitp);
}

void VerilatedVcd::set_time_resolution (const char* unitp) {
    //cout<<"set_time_resolution ("<<unitp<<") == "<<timescaleToDouble(unitp)<<" == "<<doubleToTimescale(timescaleToDouble(unitp))<<endl;
    m_timeRes = timescaleToDouble(unitp);
}

double VerilatedVcd::timescaleToDouble (const char* unitp) {
    char* endp;
    double value = strtod(unitp, &endp);
    if (!value) value=1;  // On error so we allow just "ns" to return 1e-9.
    unitp=endp;
    while (*unitp && isspace(*unitp)) unitp++;
    switch (*unitp) {
    case 's': value *= 1e1; break;
    case 'm': value *= 1e-3; break;
    case 'u': value *= 1e-6; break;
    case 'n': value *= 1e-9; break;
    case 'p': value *= 1e-12; break;
    case 'f': value *= 1e-15; break;
    case 'a': value *= 1e-18; break;
    }
    return value;
}

string VerilatedVcd::doubleToTimescale (double value) {
    const char* suffixp = "s";
    if	    (value>=1e0)   { suffixp="s"; value *= 1e0; }
    else if (value>=1e-3 ) { suffixp="ms"; value *= 1e3; }
    else if (value>=1e-6 ) { suffixp="us"; value *= 1e6; }
    else if (value>=1e-9 ) { suffixp="ns"; value *= 1e9; }
    else if (value>=1e-12) { suffixp="ps"; value *= 1e12; }
    else if (value>=1e-15) { suffixp="fs"; value *= 1e15; }
    else if (value>=1e-18) { suffixp="as"; value *= 1e18; }
    char valuestr[100]; sprintf(valuestr,"%3.0f%s", value, suffixp);
    return valuestr;  // Gets converted to string, so no ref to stack
}

//=============================================================================
// Definitions

void VerilatedVcd::printIndent (int level_change) {
    if (level_change<0) m_modDepth += level_change;
    assert(m_modDepth>=0);
    for (int i=0; i<m_modDepth; i++) printStr(" ");
    if (level_change>0) m_modDepth += level_change;
}

void VerilatedVcd::dumpHeader () {
    printStr("$version Generated by VerilatedVcd $end\n");
    time_t time_str = time(NULL);
    printStr("$date "); printStr(ctime(&time_str)); printStr(" $end\n");

    printStr("$timescale ");
    const string& timeResStr = doubleToTimescale(m_timeRes);
    printStr(timeResStr.c_str());
    printStr(" $end\n");

    makeNameMap();

    // Signal header
    assert (m_modDepth==0);
    printIndent(1);
    printStr("\n");

    // We detect the spaces in module names to determine hierarchy.  This
    // allows signals to be declared without fixed ordering, which is
    // required as Verilog signals might be separately declared from
    // "SP_TRACE" signals.

    // Print the signal names
    const char* lastName = "";
    for (NameMap::iterator it=m_namemapp->begin(); it!=m_namemapp->end(); ++it) {
	const string& hiernamestr = it->first;
	const string& decl = it->second;

	// Determine difference between the old and new names
	const char* hiername = hiernamestr.c_str();
	const char* lp = lastName;
	const char* np = hiername;
	lastName = hiername;

	// Skip common prefix, it must break at a space or tab
	for (; *np && (*np == *lp); np++, lp++) {}
	while (np!=hiername && *np && *np!=' ' && *np!='\t') { np--; lp--; }
	//printf("hier %s\n  lp=%s\n  np=%s\n",hiername,lp,np);

	// Any extra spaces in last name are scope ups we need to do
	bool first = true;
	for (; *lp; lp++) {
	    if (*lp==' ' || (first && *lp!='\t')) {
		printIndent(-1);
		printStr("$upscope $end\n");
	    }
	    first = false;
	}

	// Any new spaces are scope downs we need to do
	while (*np) {
	    if (*np==' ') np++;
	    if (*np=='\t') break; // tab means signal name starts
	    printIndent(1);
	    printStr("$scope module ");
	    for (; *np && *np!=' ' && *np!='\t'; np++) {
		if (*np=='[') printStr("(");
		else if (*np==']') printStr(")");
		else *m_writep++=*np;
	    }
	    printStr(" $end\n");
	}

	printIndent(0);
	printStr(decl.c_str());
    }

    while (m_modDepth>1) {
	printIndent(-1);
	printStr("$upscope $end\n");
    }

    printIndent(-1);
    printStr("$enddefinitions $end\n\n\n");
    assert (m_modDepth==0);

    // Reclaim storage
    deleteNameMap();
}

void VerilatedVcd::module (const string& name) {
    m_modName = name;
}

void VerilatedVcd::declare (vluint32_t code, const char* name, const char* wirep,
			    int arraynum, bool tri, bool bussed, int msb, int lsb) {
    if (!code) { vl_fatal(__FILE__,__LINE__,"","Internal: internal trace problem, code 0 is illegal"); }

    int bits = ((msb>lsb)?(msb-lsb):(lsb-msb))+1;
    int codesNeeded = 1+int(bits/32);
    if (tri) codesNeeded *= 2;   // Space in change array for __en signals

    // Make sure array is large enough
    m_nextCode = max(nextCode(), code+codesNeeded);
    if (m_sigs.capacity() <= m_nextCode) {
	m_sigs.reserve(m_nextCode*2);	// Power-of-2 allocation speeds things up
    }

    // Make sure write buffer is large enough (one character per bit), plus header
    bufferResize(bits+1024);

    // Save declaration info
    VerilatedVcdSig sig = VerilatedVcdSig(code, bits);
    m_sigs.push_back(sig);

    // Split name into basename
    // Spaces and tabs aren't legal in VCD signal names, so:
    // Space separates each level of scope
    // Tab separates final scope from signal name
    // Tab sorts before spaces, so signals nicely will print before scopes
    // Note the hiername may be nothing, if so we'll add "\t{name}"
    string nameasstr = name;
    if (m_modName!="") { nameasstr = m_modName+m_scopeEscape+nameasstr; }  // Optional ->module prefix
    string hiername;
    string basename;
    for (const char* cp=nameasstr.c_str(); *cp; cp++) {
	if (isScopeEscape(*cp)) {
	    // Ahh, we've just read a scope, not a basename
	    if (hiername!="") hiername += " ";
	    hiername += basename;
	    basename = "";
	} else {
	    basename += *cp;
	}
    }
    hiername += "\t"+basename;

    // Print reference
    string decl = "$var ";
    if (m_evcd) decl += "port"; else decl += wirep;  // usually "wire"
    char buf [1000];
    sprintf(buf, " %2d ", bits);
    decl += buf;
    if (m_evcd) {
	sprintf(buf, "<%d", code);
	decl += buf;
    } else {
	decl += stringCode(code);
    }
    decl += " ";
    decl += basename;
    if (arraynum>=0) {
	sprintf(buf, "(%d)", arraynum);
	decl += buf;
	hiername += buf;
    }
    if (bussed) {
	sprintf(buf, " [%d:%d]", msb, lsb);
	decl += buf;
    }
    decl += " $end\n";
    m_namemapp->insert(make_pair(hiername,decl));
}

void VerilatedVcd::declBit      (vluint32_t code, const char* name, int arraynum)
{  declare (code, name, "wire", arraynum, false, false, 0, 0); }
void VerilatedVcd::declBus      (vluint32_t code, const char* name, int arraynum, int msb, int lsb)
{  declare (code, name, "wire", arraynum, false, true, msb, lsb); }
void VerilatedVcd::declQuad     (vluint32_t code, const char* name, int arraynum, int msb, int lsb)
{  declare (code, name, "wire", arraynum, false, true, msb, lsb); }
void VerilatedVcd::declArray    (vluint32_t code, const char* name, int arraynum, int msb, int lsb)
{  declare (code, name, "wire", arraynum, false, true, msb, lsb); }
void VerilatedVcd::declTriBit   (vluint32_t code, const char* name, int arraynum)
{  declare (code, name, "wire", arraynum, true, false, 0, 0); }
void VerilatedVcd::declTriBus   (vluint32_t code, const char* name, int arraynum, int msb, int lsb)
{  declare (code, name, "wire", arraynum, true, true, msb, lsb); }
void VerilatedVcd::declTriQuad  (vluint32_t code, const char* name, int arraynum, int msb, int lsb)
{  declare (code, name, "wire", arraynum, true, true, msb, lsb); }
void VerilatedVcd::declTriArray (vluint32_t code, const char* name, int arraynum, int msb, int lsb)
{  declare (code, name, "wire", arraynum, true, true, msb, lsb); }
void VerilatedVcd::declFloat    (vluint32_t code, const char* name, int arraynum)
{  declare (code, name, "real", arraynum, false, false, 31, 0); }
void VerilatedVcd::declDouble   (vluint32_t code, const char* name, int arraynum)
{  declare (code, name, "real", arraynum, false, false, 63, 0); }

//=============================================================================

void VerilatedVcd::fullDouble (vluint32_t code, const double newval) {
    (*((double*)&m_sigs_oldvalp[code])) = newval;
    // Buffer can't overflow before sprintf; we sized during declaration
    sprintf(m_writep, "r%.16g", newval);
    m_writep += strlen(m_writep);
    *m_writep++=' '; printCode(code); *m_writep++='\n';
    bufferCheck();
}
void VerilatedVcd::fullFloat (vluint32_t code, const float newval) {
    (*((float*)&m_sigs_oldvalp[code])) = newval;
    // Buffer can't overflow before sprintf; we sized during declaration
    sprintf(m_writep, "r%.16g", (double)newval);
    m_writep += strlen(m_writep);
    *m_writep++=' '; printCode(code); *m_writep++='\n';
    bufferCheck();
}

//=============================================================================
// Callbacks

void VerilatedVcd::addCallback (
    VerilatedVcdCallback_t initcb, VerilatedVcdCallback_t fullcb, VerilatedVcdCallback_t changecb,
    void* userthis)
{
    if (VL_UNLIKELY(isOpen())) {
	string msg = (string)"Internal: "+__FILE__+"::"+__FUNCTION__+" called with already open file";
	vl_fatal(__FILE__,__LINE__,"",msg.c_str());
    }
    VerilatedVcdCallInfo* vci = new VerilatedVcdCallInfo(initcb, fullcb, changecb, userthis, nextCode());
    m_callbacks.push_back(vci);
}

//=============================================================================
// Dumping

void VerilatedVcd::dumpFull (vluint64_t timeui) {
    dumpPrep (timeui);
    for (vluint32_t ent = 0; ent< m_callbacks.size(); ent++) {
	VerilatedVcdCallInfo *cip = m_callbacks[ent];
	(cip->m_fullcb) (this, cip->m_userthis, cip->m_code);
    }
    dumpDone ();
}

void VerilatedVcd::dump (vluint64_t timeui) {
    if (!isOpen()) return;
    if (VL_UNLIKELY(m_fullDump)) {
	m_fullDump = false;	// No need for more full dumps
	dumpFull(timeui);
	return;
    }
    if (VL_UNLIKELY(m_rolloverMB && m_wroteBytes > this->m_rolloverMB)) {
	openNext(true);
	if (!isOpen()) return;
    }
    dumpPrep (timeui);
    for (vluint32_t ent = 0; ent< m_callbacks.size(); ent++) {
	VerilatedVcdCallInfo *cip = m_callbacks[ent];
	(cip->m_changecb) (this, cip->m_userthis, cip->m_code);
    }
    dumpDone();
}

void VerilatedVcd::dumpPrep (vluint64_t timeui) {
    printStr("#");
    printTime(timeui);
    printStr("\n");
}

void VerilatedVcd::dumpDone () {
}

//======================================================================
// Static members

void VerilatedVcd::flush_all() {
    for (vluint32_t ent = 0; ent< s_vcdVecp.size(); ent++) {
	VerilatedVcd* vcdp = s_vcdVecp[ent];
	vcdp->flush();
    }
}

//======================================================================
//======================================================================
//======================================================================

#ifdef VERILATED_VCD_TEST
vluint32_t v1, v2, s1, s2[3];
vluint32_t tri96[3];
vluint32_t tri96__tri[3];
vluint8_t ch;
vluint64_t timestamp = 1;
double doub = 0;

void vcdInit (VerilatedVcd* vcdp, void* userthis, vluint32_t code) {
    vcdp->scopeEscape('.');
    vcdp->module ("top");
     vcdp->declBus (0x2, "v1",-1,5,1);
     vcdp->declBus (0x3, "v2",-1,6,0);
     vcdp->module ("top.sub1");
      vcdp->declBit (0x4, "s1",-1);
      vcdp->declBit (0x5, "ch",-1);
     vcdp->module ("top.sub2");
      vcdp->declArray (0x6, "s2",-1, 40,3);
    // Note need to add 3 for next code.
    vcdp->module ("top2");
     vcdp->declBus (0x2, "t2v1",-1,4,1);
     vcdp->declTriBit   (0x10, "io1", -1);
     vcdp->declTriBus   (0x12, "io5", -1,4,0);
     vcdp->declTriArray (0x16, "io96",-1,95,0);
    // Note need to add 6 for next code.
     vcdp->declDouble   (0x1c, "doub",-1);
    // Note need to add 2 for next code.
}

void vcdFull (VerilatedVcd* vcdp, void* userthis, vluint32_t code) {
    vcdp->fullBus  (0x2, v1,5);
    vcdp->fullBus  (0x3, v2,7);
    vcdp->fullBit  (0x4, s1);
    vcdp->fullBus  (0x5, ch,2);
    vcdp->fullArray(0x6, &s2[0], 38);
    vcdp->fullTriBit   (0x10, tri96[0]&1,    tri96__tri[0]&1);
    vcdp->fullTriBus   (0x12, tri96[0]&0x1f, tri96__tri[0]&0x1f,  5);
    vcdp->fullTriArray (0x16, tri96,         tri96__tri,          96);
    vcdp->fullDouble(0x1c, doub);
}

void vcdChange (VerilatedVcd* vcdp, void* userthis, vluint32_t code) {
    vcdp->chgBus  (0x2, v1,5);
    vcdp->chgBus  (0x3, v2,7);
    vcdp->chgBit  (0x4, s1);
    vcdp->chgBus  (0x5, ch,2);
    vcdp->chgArray(0x6, &s2[0], 38);
    vcdp->chgTriBit   (0x10, tri96[0]&1,   tri96__tri[0]&1);
    vcdp->chgTriBus   (0x12, tri96[0]&0x1f, tri96__tri[0]&0x1f, 5);
    vcdp->chgTriArray (0x16, tri96,         tri96__tri,         96);
    vcdp->chgDouble   (0x1c, doub);
}

main() {
    cout<<"test: O_LARGEFILE="<<O_LARGEFILE<<endl;

    v1 = v2 = s1 = 0;
    s2[0] = s2[1] = s2[2] = 0;
    tri96[2] = tri96[1] = tri96[0] = 0;
    tri96__tri[2] = tri96__tri[1] = tri96__tri[0] = ~0;
    ch = 0;
    doub = 0;
    {
	VerilatedVcdC* vcdp = new VerilatedVcdC;
	vcdp->spTrace()->addCallback (&vcdInit, &vcdFull, &vcdChange, 0);
	vcdp->open ("test.vcd");
	// Dumping
	vcdp->dump(timestamp++);
	v1 = 0xfff;
	tri96[2] = 4; tri96[1] = 2; tri96[0] = 1;
	tri96__tri[2] = tri96__tri[1] = tri96__tri[0] = ~0;  // Still tri
	doub = 1.5;
	vcdp->dump(timestamp++);
	v2 = 0x1;
	s2[1] = 2;
	tri96__tri[2] = tri96__tri[1] = tri96__tri[0] = 0; // enable w/o data change
	doub = -1.66e13;
	vcdp->dump(timestamp++);
	ch = 2;
	tri96[2] = ~4; tri96[1] = ~2; tri96[0] = ~1;
	doub = -3.33e-13;
	vcdp->dump(timestamp++);
	vcdp->dump(timestamp++);
# ifdef VERILATED_VCD_TEST_64BIT
	vluint64_t bytesPerDump = 15ULL;
	for (vluint64_t i=0; i<((1ULL<<32) / bytesPerDump); i++) {
	    v1 = i;
	    vcdp->dump(timestamp++);
	}
# endif
	vcdp->close();
    }
}
#endif

//********************************************************************
// Local Variables:
// compile-command: "mkdir -p ../test_dir && cd ../test_dir && c++ -DVERILATED_VCD_TEST ../src/verilated_vcd_c.cpp -o verilated_vcd_c && ./verilated_vcd_c && cat test.vcd"
// End:
