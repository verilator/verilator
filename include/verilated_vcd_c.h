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

#ifndef _VERILATED_VCD_C_H_
#define _VERILATED_VCD_C_H_ 1

#include "verilatedos.h"

#include <string>
#include <vector>
#include <map>
using namespace std;

class VerilatedVcd;
class VerilatedVcdCallInfo;

// SPDIFF_ON
//=============================================================================
// VerilatedFile
/// File handling routines, which can be overrode for e.g. socket I/O

class VerilatedVcdFile {
private:
    int			m_fd;		///< File descriptor we're writing to
public:
    // METHODS
    VerilatedVcdFile() : m_fd(0) {}
    virtual ~VerilatedVcdFile() {}
    virtual bool open(const string& name);
    virtual void close();
    virtual ssize_t write(const char* bufp, ssize_t len);
};

//=============================================================================
// VerilatedVcdSig
/// Internal data on one signal being traced.

class VerilatedVcdSig {
protected:
    friend class VerilatedVcd;
    vluint32_t		m_code;		///< VCD file code number
    int			m_bits;		///< Size of value in bits
    VerilatedVcdSig (vluint32_t code, int bits)
	: m_code(code), m_bits(bits) {}
public:
    ~VerilatedVcdSig() {}
};

//=============================================================================

typedef void (*VerilatedVcdCallback_t)(VerilatedVcd* vcdp, void* userthis, vluint32_t code);

//=============================================================================
// VerilatedVcd
/// Base class to create a Verilator VCD dump
/// This is an internally used class - see VerilatedVcdC for what to call from applications

class VerilatedVcd {
private:
    VerilatedVcdFile*	m_filep;	///< File we're writing to
    bool		m_fileNewed;	///< m_filep needs destruction
    bool 		m_isOpen;	///< True indicates open file
    bool		m_evcd;		///< True for evcd format
    string		m_filename;	///< Filename we're writing to (if open)
    vluint64_t		m_rolloverMB;	///< MB of file size to rollover at
    char		m_scopeEscape;	///< Character to separate scope components
    int			m_modDepth;	///< Depth of module hierarchy
    bool		m_fullDump;	///< True indicates dump ignoring if changed
    vluint32_t		m_nextCode;	///< Next code number to assign
    string		m_modName;	///< Module name being traced now
    double		m_timeRes;	///< Time resolution (ns/ms etc)
    double		m_timeUnit;	///< Time units (ns/ms etc)
    vluint64_t		m_timeLastDump;	///< Last time we did a dump

    char*		m_wrBufp;	///< Output buffer
    char*		m_wrFlushp;	///< Output buffer flush trigger location
    char*		m_writep;	///< Write pointer into output buffer
    vluint64_t		m_wrChunkSize;	///< Output buffer size
    vluint64_t		m_wroteBytes;	///< Number of bytes written to this file

    vluint32_t*			m_sigs_oldvalp;	///< Pointer to old signal values
    vector<VerilatedVcdSig>	m_sigs;		///< Pointer to signal information
    vector<VerilatedVcdCallInfo*>	m_callbacks;	///< Routines to perform dumping
    typedef map<string,string>	NameMap;
    NameMap*			m_namemapp;	///< List of names for the header
    static vector<VerilatedVcd*>	s_vcdVecp;	///< List of all created traces

    void bufferResize(vluint64_t minsize);
    void bufferFlush();
    inline void bufferCheck() {
	// Flush the write buffer if there's not enough space left for new information
	// We only call this once per vector, so we need enough slop for a very wide "b###" line
	if (VL_UNLIKELY(m_writep > m_wrFlushp)) {
	    bufferFlush();
	}
    }
    void closePrev();
    void closeErr();
    void openNext();
    void makeNameMap();
    void deleteNameMap();
    void printIndent (int levelchange);
    void printStr (const char* str);
    void printQuad (vluint64_t n);
    void printTime (vluint64_t timeui);
    void declare (vluint32_t code, const char* name, const char* wirep,
		  int arraynum, bool tri, bool bussed, int msb, int lsb);

    void dumpHeader();
    void dumpPrep (vluint64_t timeui);
    void dumpFull (vluint64_t timeui);
    // cppcheck-suppress functionConst
    void dumpDone ();
    inline void printCode (vluint32_t code) {
	if (code>=(94*94*94)) *m_writep++ = ((char)((code/94/94/94)%94+33));
	if (code>=(94*94))    *m_writep++ = ((char)((code/94/94)%94+33));
	if (code>=(94))       *m_writep++ = ((char)((code/94)%94+33));
	*m_writep++ = ((char)((code)%94+33));
    }
    static string stringCode (vluint32_t code) {
	string out;
	if (code>=(94*94*94)) out += ((char)((code/94/94/94)%94+33));
	if (code>=(94*94))    out += ((char)((code/94/94)%94+33));
	if (code>=(94))       out += ((char)((code/94)%94+33));
	return out + ((char)((code)%94+33));
    }

protected:
    // METHODS
    void evcd(bool flag) { m_evcd = flag; }

public:
    // CREATORS
    VerilatedVcd(VerilatedVcdFile* filep=NULL);
    ~VerilatedVcd();

    // ACCESSORS
    /// Inside dumping routines, return next VCD signal code
    vluint32_t nextCode() const {return m_nextCode;}
    /// Set size in megabytes after which new file should be created
    void rolloverMB(vluint64_t rolloverMB) { m_rolloverMB=rolloverMB; };
    /// Is file open?
    bool isOpen() const { return m_isOpen; }
    /// Change character that splits scopes.  Note whitespace are ALWAYS escapes.
    void scopeEscape(char flag) { m_scopeEscape = flag; }
    /// Is this an escape?
    inline bool isScopeEscape(char c) { return isspace(c) || c==m_scopeEscape; }

    // METHODS
    void open (const char* filename);	///< Open the file; call isOpen() to see if errors
    void openNext (bool incFilename);	///< Open next data-only file
    void flush() { bufferFlush(); }	///< Flush any remaining data
    static void flush_all();		///< Flush any remaining data from all files
    void close ();			///< Close the file

    void set_time_unit (const char* unit); ///< Set time units (s/ms, defaults to ns)
    void set_time_unit (const string& unit) { set_time_unit(unit.c_str()); }

    void set_time_resolution (const char* unit); ///< Set time resolution (s/ms, defaults to ns)
    void set_time_resolution (const string& unit) { set_time_resolution(unit.c_str()); }

    double timescaleToDouble (const char* unitp);
    string doubleToTimescale (double value);

    /// Inside dumping routines, called each cycle to make the dump
    void dump     (vluint64_t timeui);
    /// Call dump with a absolute unscaled time in seconds
    void dumpSeconds (double secs) { dump((vluint64_t)(secs * m_timeRes)); }

    /// Inside dumping routines, declare callbacks for tracings
    void addCallback (VerilatedVcdCallback_t init, VerilatedVcdCallback_t full,
		      VerilatedVcdCallback_t change,
		      void* userthis);

    /// Inside dumping routines, declare a module
    void module (const string& name);
    /// Inside dumping routines, declare a signal
    void declBit      (vluint32_t code, const char* name, int arraynum);
    void declBus      (vluint32_t code, const char* name, int arraynum, int msb, int lsb);
    void declQuad     (vluint32_t code, const char* name, int arraynum, int msb, int lsb);
    void declArray    (vluint32_t code, const char* name, int arraynum, int msb, int lsb);
    void declTriBit   (vluint32_t code, const char* name, int arraynum);
    void declTriBus   (vluint32_t code, const char* name, int arraynum, int msb, int lsb);
    void declTriQuad  (vluint32_t code, const char* name, int arraynum, int msb, int lsb);
    void declTriArray (vluint32_t code, const char* name, int arraynum, int msb, int lsb);
    void declDouble   (vluint32_t code, const char* name, int arraynum);
    void declFloat    (vluint32_t code, const char* name, int arraynum);
    //	... other module_start for submodules (based on cell name)

    /// Inside dumping routines, dump one signal
    void fullBit (vluint32_t code, const vluint32_t newval) {
	// Note the &1, so we don't require clean input -- makes more common no change case faster
	m_sigs_oldvalp[code] = newval;
	*m_writep++=('0'+(char)(newval&1)); printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullBus (vluint32_t code, const vluint32_t newval, int bits) {
	m_sigs_oldvalp[code] = newval;
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    *m_writep++=((newval&(1L<<bit))?'1':'0');
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullQuad (vluint32_t code, const vluint64_t newval, int bits) {
	(*((vluint64_t*)&m_sigs_oldvalp[code])) = newval;
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    *m_writep++=((newval&(1ULL<<bit))?'1':'0');
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullArray (vluint32_t code, const vluint32_t* newval, int bits) {
	for (int word=0; word<(((bits-1)/32)+1); ++word) {
	    m_sigs_oldvalp[code+word] = newval[word];
	}
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    *m_writep++=((newval[(bit/32)]&(1L<<(bit&0x1f)))?'1':'0');
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullTriBit (vluint32_t code, const vluint32_t newval, const vluint32_t newtri) {
	m_sigs_oldvalp[code]   = newval;
	m_sigs_oldvalp[code+1] = newtri;
	*m_writep++ = "01zz"[m_sigs_oldvalp[code]
			     | (m_sigs_oldvalp[code+1]<<1)];
	printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullTriBus (vluint32_t code, const vluint32_t newval, const vluint32_t newtri, int bits) {
	m_sigs_oldvalp[code] = newval;
	m_sigs_oldvalp[code+1] = newtri;
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    *m_writep++ = "01zz"[((newval >> bit)&1)
				 | (((newtri >> bit)&1)<<1)];
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullTriQuad (vluint32_t code, const vluint64_t newval, const vluint32_t newtri, int bits) {
	(*((vluint64_t*)&m_sigs_oldvalp[code])) = newval;
	(*((vluint64_t*)&m_sigs_oldvalp[code+1])) = newtri;
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    *m_writep++ = "01zz"[((newval >> bit)&1ULL)
				 | (((newtri >> bit)&1ULL)<<1ULL)];
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullTriArray (vluint32_t code, const vluint32_t* newvalp, const vluint32_t* newtrip, int bits) {
	for (int word=0; word<(((bits-1)/32)+1); ++word) {
	    m_sigs_oldvalp[code+word*2]   = newvalp[word];
	    m_sigs_oldvalp[code+word*2+1] = newtrip[word];
	}
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    vluint32_t valbit = (newvalp[(bit/32)]>>(bit&0x1f)) & 1;
	    vluint32_t tribit = (newtrip[(bit/32)]>>(bit&0x1f)) & 1;
	    *m_writep++ = "01zz"[valbit | (tribit<<1)];
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    void fullDouble (vluint32_t code, const double newval);
    void fullFloat (vluint32_t code, const float newval);

    /// Inside dumping routines, dump one signal as unknowns
    /// Presently this code doesn't change the oldval vector.
    /// Thus this is for special standalone applications that after calling
    /// fullBitX, must when then value goes non-X call fullBit.
    inline void fullBitX (vluint32_t code) {
	*m_writep++='x'; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    inline void fullBusX (vluint32_t code, int bits) {
	*m_writep++='b';
	for (int bit=bits-1; bit>=0; --bit) {
	    *m_writep++='x';
	}
	*m_writep++=' '; printCode(code); *m_writep++='\n';
	bufferCheck();
    }
    inline void fullQuadX (vluint32_t code, int bits) { fullBusX (code, bits); }
    inline void fullArrayX (vluint32_t code, int bits) { fullBusX (code, bits); }

    /// Inside dumping routines, dump one signal if it has changed
    inline void chgBit (vluint32_t code, const vluint32_t newval) {
	vluint32_t diff = m_sigs_oldvalp[code] ^ newval;
	if (VL_UNLIKELY(diff)) {
	    // Verilator 3.510 and newer provide clean input, so the below is only for back compatibility
	    if (VL_UNLIKELY(diff & 1)) {   // Change after clean?
		fullBit (code, newval);
	    }
	}
    }
    inline void chgBus (vluint32_t code, const vluint32_t newval, int bits) {
	vluint32_t diff = m_sigs_oldvalp[code] ^ newval;
	if (VL_UNLIKELY(diff)) {
	    if (VL_UNLIKELY(bits==32 || (diff & ((1U<<bits)-1) ))) {
		fullBus (code, newval, bits);
	    }
	}
    }
    inline void chgQuad (vluint32_t code, const vluint64_t newval, int bits) {
	vluint64_t diff = (*((vluint64_t*)&m_sigs_oldvalp[code])) ^ newval;
	if (VL_UNLIKELY(diff)) {
	    if (VL_UNLIKELY(bits==64 || (diff & ((1ULL<<bits)-1) ))) {
		fullQuad(code, newval, bits);
	    }
	}
    }
    inline void chgArray (vluint32_t code, const vluint32_t* newval, int bits) {
	for (int word=0; word<(((bits-1)/32)+1); ++word) {
	    if (VL_UNLIKELY(m_sigs_oldvalp[code+word] ^ newval[word])) {
		fullArray (code,newval,bits);
		return;
	    }
	}
    }
    inline void chgTriBit (vluint32_t code, const vluint32_t newval, const vluint32_t newtri) {
	vluint32_t diff = ((m_sigs_oldvalp[code] ^ newval)
			 | (m_sigs_oldvalp[code+1] ^ newtri));
	if (VL_UNLIKELY(diff)) {
	    // Verilator 3.510 and newer provide clean input, so the below is only for back compatibility
	    if (VL_UNLIKELY(diff & 1)) {   // Change after clean?
		fullTriBit (code, newval, newtri);
	    }
	}
    }
    inline void chgTriBus (vluint32_t code, const vluint32_t newval, const vluint32_t newtri, int bits) {
	vluint32_t diff = ((m_sigs_oldvalp[code] ^ newval)
			 | (m_sigs_oldvalp[code+1] ^ newtri));
	if (VL_UNLIKELY(diff)) {
	    if (VL_UNLIKELY(bits==32 || (diff & ((1U<<bits)-1) ))) {
		fullTriBus (code, newval, newtri, bits);
	    }
	}
    }
    inline void chgTriQuad (vluint32_t code, const vluint64_t newval, const vluint32_t newtri, int bits) {
	vluint64_t diff = ( ((*((vluint64_t*)&m_sigs_oldvalp[code])) ^ newval)
			  | ((*((vluint64_t*)&m_sigs_oldvalp[code+1])) ^ newtri));
	if (VL_UNLIKELY(diff)) {
	    if (VL_UNLIKELY(bits==64 || (diff & ((1ULL<<bits)-1) ))) {
		fullTriQuad(code, newval, newtri, bits);
	    }
	}
    }
    inline void chgTriArray (vluint32_t code, const vluint32_t* newvalp, const vluint32_t* newtrip, int bits) {
	for (int word=0; word<(((bits-1)/32)+1); ++word) {
	    if (VL_UNLIKELY((m_sigs_oldvalp[code+word*2] ^ newvalp[word])
			    | (m_sigs_oldvalp[code+word*2+1] ^ newtrip[word]))) {
		fullTriArray (code,newvalp,newtrip,bits);
		return;
	    }
	}
    }
    inline void chgDouble (vluint32_t code, const double newval) {
	if (VL_UNLIKELY((*((double*)&m_sigs_oldvalp[code])) != newval)) {
	    fullDouble (code, newval);
	}
    }
    inline void chgFloat (vluint32_t code, const float newval) {
	if (VL_UNLIKELY((*((float*)&m_sigs_oldvalp[code])) != newval)) {
	    fullFloat (code, newval);
	}
    }
};

//=============================================================================
// VerilatedVcdC
/// Create a VCD dump file in C standalone (no SystemC) simulations.

class VerilatedVcdC {
    VerilatedVcd		m_sptrace;	///< Trace file being created
public:
    // CONSTRUCTORS
    VerilatedVcdC(VerilatedVcdFile* filep=NULL) : m_sptrace(filep) {}
    ~VerilatedVcdC() {}
    // ACCESSORS
    /// Is file open?
    bool isOpen() const { return m_sptrace.isOpen(); }
    // METHODS
    /// Open a new VCD file
    /// This includes a complete header dump each time it is called,
    /// just as if this object was deleted and reconstructed.
    void open (const char* filename) { m_sptrace.open(filename); }
    /// Continue a VCD dump by rotating to a new file name
    /// The header is only in the first file created, this allows
    /// "cat" to be used to combine the header plus any number of data files.
    void openNext (bool incFilename=true) { m_sptrace.openNext(incFilename); }
    /// Set size in megabytes after which new file should be created
    void rolloverMB(size_t rolloverMB) { m_sptrace.rolloverMB(rolloverMB); };
    /// Close dump
    void close() { m_sptrace.close(); }
    /// Flush dump
    void flush() { m_sptrace.flush(); }
    /// Write one cycle of dump data
    void dump (vluint64_t timeui) { m_sptrace.dump(timeui); }
    /// Write one cycle of dump data - backward compatible and to reduce
    /// conversion warnings.  It's better to use a vluint64_t time instead.
    void dump (double timestamp) { dump((vluint64_t)timestamp); }
    void dump (vluint32_t timestamp) { dump((vluint64_t)timestamp); }
    void dump (int timestamp) { dump((vluint64_t)timestamp); }
    /// Internal class access
    inline VerilatedVcd* spTrace () { return &m_sptrace; };
};

#endif // guard
