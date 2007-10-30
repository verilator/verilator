// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Large 4-state numbers
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

#include <config_build.h>
#include "verilatedos.h"
#include <math.h>
#include <stdio.h>
#include <stdarg.h>
#include <algorithm>
#include "V3Number.h"

//######################################################################
// Read class functions
// CREATION

void V3Number::width(int width, bool sized) {
    // Set width.  Only set m_width here, as we need to tweak vector size
    if (width) { m_sized = sized; m_width=width; }
    else { m_sized = false; m_width=1; }
    if (m_value.size() < (unsigned)(words()+1)) {
	m_value.resize(words()+1);
	m_valueX.resize(words()+1);
    }
}

void V3Number::init (FileLine* fileline, int swidth) {
    m_fileline = fileline;
    m_signed = false;
    m_autoExtend = false;
    width(swidth);
    for (int i=0; i<words(); i++) m_value[i]=m_valueX[i] = 0;
}

V3Number::V3Number(VerilogString, FileLine* fileline, const string& str) {
    // Create a number using a verilog string as the value, thus 8 bits per character.
    init(fileline, str.length()*8);
    for (unsigned pos=0; pos<str.length(); ++pos) {
	int topos = str.length()-1-pos;
	for (int bit=0; bit<8; ++bit) {
	    if (str[pos] & (1UL<<bit)) {
		m_value[topos/4] |= (1UL<<(bit + (topos%4)*8));
	    }
	}
    }
}

V3Number::V3Number (FileLine* fileline, const char* sourcep) {
    init(fileline, 0);
    const char* value_startp = sourcep;
    for (const char* cp=sourcep; *cp; cp++) {
	if (*cp == '\'') {
	    value_startp = cp+1;
	    break;
	}
    }

    bool unbased = false;
    char base = '\0';
    if (value_startp != sourcep) {	// Has a '
	char widthn[100]; char* wp=&widthn[0];
	const char* cp=sourcep;
	for (; *cp; cp++) {
	    if (*cp == '\'') { cp++ ; break; }
	    if (*cp != '_') *wp++ = *cp;
	}
	*wp++ = '\0';
	while (*cp && *cp == '_') cp++;
	if (*cp && tolower(*cp)=='s') {
	    cp++; isSigned(true);
	}
	if (*cp) { base=*cp; cp++; }
	value_startp = cp;

	if (atoi(widthn)) {
	    width(atoi(widthn), true);
	}
    } else {
	unbased = true;
	base = 'd';
    }
    
    for (int i=0; i<words(); i++) m_value[i]=m_valueX[i] = 0;

    // Special SystemVerilog unsized constructs
    if (base == '0') {
	setBit(0, 0); width(1, false);	// So we extend it
	m_autoExtend = true;
    } else if (base == '1') {
	setBit(0, 1); width(1, false);	// So we extend it
	m_autoExtend = true;
    } else if (tolower(base) == 'z') {
	setBit(0, 'z'); width(1, false);	// So we extend it
	m_autoExtend = true;
    } else if (tolower(base) == 'x') {
	setBit(0, 'x'); width(1, false);	// So we extend it
	m_autoExtend = true;
    } 
    // Otherwise...
    else if (!m_sized) {
	width(32, false); // Says the spec.
	if (unbased) isSigned(true); // Also says the spec.
    }

    // Ignore leading blanks
    while (*value_startp=='_' || isspace(*value_startp)) value_startp++;

    int obit = 0;  // Start at LSB
    if (tolower(base) == 'd') {
	// Ignore leading zeros so we don't issue too many digit errors when lots of leading 0's
	while (*value_startp=='_' || *value_startp=='0') value_startp++;
	// Convert decimal number to hex
	int olen = 0;
	uint32_t val = 0;
	for (const char* cp=value_startp;
	     *cp; cp++) {
	    switch (tolower(*cp)) {
	    case '0': case '1': case '2': case '3': case '4':
	    case '5': case '6': case '7': case '8': case '9': {
		val = val*10 + (*cp-'0');
		m_value[0] = val;
		if (width()>32 && olen>7/*10000000 fits in 32 bits, so ok*/) {
		    m_fileline->v3error("Unsupported: Conversion of decimal number over 32 bits, use hex\n");
		    olen=0;
		}
		olen++;
		break;
	    }
	    case 'z': {
		if (olen) m_fileline->v3error("Multi-digit X/Z/? not legal in decimal constant: "<<*cp);
		if (!m_sized)  m_fileline->v3error("Unsized X/Z/? not legal in decimal constant: "<<*cp);
		olen++;
		setAllBitsZ();
		break;
	    }
	    case 'x': case '?': {
		if (olen) m_fileline->v3error("Multi-digit X/Z/? not legal in decimal constant: "<<*cp);
		if (!m_sized)  m_fileline->v3error("Unsized X/Z/? not legal in decimal constant: "<<*cp);
		olen++;
		setAllBitsX();
		break;
	    }
	    case '_': break;
	    default: {
		m_fileline->v3error("Illegal character in decimal constant: "<<*cp);
		break;
	    }
	    }
	}
	obit = width();
    }
    else {
	// Convert bin/octal number to hex
	for (const char* cp=value_startp+strlen(value_startp)-1;
	     (cp>=value_startp
	      && obit<=width());
	     cp--) {
	    if (*cp!='_' && obit>=width()) {
		m_fileline->v3error("Too many digits for "<<width()<<" bit number: "<<sourcep);
		break;
	    }
	    switch(tolower(base)) {
	    case 'b': {
		switch(tolower(*cp)) {
		case '0': setBit(obit++, 0); break;
		case '1': setBit(obit++, 1); break;
		case 'z': setBit(obit++, 'z'); break;
		case 'x': case '?':
		    setBit(obit++, 'x'); break;
		case '_': break;
		default:
		    m_fileline->v3error("Illegal character in binary constant: "<<*cp);
		}
	    break;
	    }
	    
	    case 'o':
	    case 'c': {
		switch(tolower(*cp)) {
		case '0': setBit(obit++, 0); setBit(obit++, 0);  setBit(obit++, 0);  break;
		case '1': setBit(obit++, 1); setBit(obit++, 0);  setBit(obit++, 0);  break;
		case '2': setBit(obit++, 0); setBit(obit++, 1);  setBit(obit++, 0);  break;
		case '3': setBit(obit++, 1); setBit(obit++, 1);  setBit(obit++, 0);  break;
		case '4': setBit(obit++, 0); setBit(obit++, 0);  setBit(obit++, 1);  break;
		case '5': setBit(obit++, 1); setBit(obit++, 0);  setBit(obit++, 1);  break;
		case '6': setBit(obit++, 0); setBit(obit++, 1);  setBit(obit++, 1);  break;
		case '7': setBit(obit++, 1); setBit(obit++, 1);  setBit(obit++, 1);  break;
		case 'z': setBit(obit++, 'z'); setBit(obit++, 'z');  setBit(obit++, 'z');  break;
		case 'x': case '?':
		    setBit(obit++, 'x'); setBit(obit++, 'x');  setBit(obit++, 'x');  break;
		case '_': break;
		default:
		    m_fileline->v3error("Illegal character in octal constant");
		}
		break;
	    }
	    
	    case 'h': {
		switch(tolower(*cp)) {
		case '0': setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); break;
		case '1': setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); break;
		case '2': setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); break;
		case '3': setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); break;
		case '4': setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); break;
		case '5': setBit(obit++,1); setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); break;
		case '6': setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); break;
		case '7': setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); break;
		case '8': setBit(obit++,0); setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); break;
		case '9': setBit(obit++,1); setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); break;
		case 'a': setBit(obit++,0); setBit(obit++,1); setBit(obit++,0); setBit(obit++,1);  break;
		case 'b': setBit(obit++,1); setBit(obit++,1); setBit(obit++,0); setBit(obit++,1); break;
		case 'c': setBit(obit++,0); setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); break;
		case 'd': setBit(obit++,1); setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); break;
		case 'e': setBit(obit++,0); setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); break;
		case 'f': setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); setBit(obit++,1); break;
		case 'z': setBit(obit++,'z'); setBit(obit++,'z'); setBit(obit++,'z'); setBit(obit++,'z'); break;
		case 'x': case '?':
		    setBit(obit++,'x'); setBit(obit++,'x'); setBit(obit++,'x'); setBit(obit++,'x'); break;
		case '_':  break;
		default:
		    m_fileline->v3error("Illegal character in hex constant: "<<*cp);
		}
		break;
	    }
	    default:
		m_fileline->v3error("Illegal base character: "<<base);
	    }
	}
    }

    // Z or X extend specific width values.  Spec says we don't 1 extend.
    // This fixes 2'bx to become 2'bxx.
    while (obit<=width() && obit && bitIsXZ(obit-1)) {
	setBit(obit, bitIs(obit-1));
	obit++;
    }

    //printf("Dump \"%s\"  CP \"%s\"  B '%c' %d W %d\n", sourcep, value_startp, base, width(), m_value[0]);
}

//======================================================================
// Global

int V3Number::log2b(uint32_t num) {
    for (int bit=31; bit>0; bit--) if (num & (VL_ULL(1)<<bit)) return(bit);
    return(0);
}

//======================================================================
// Setters

V3Number& V3Number::setZero() {
    for (int i=0; i<words(); i++) m_value[i]=m_valueX[i] = 0;
    return *this;
}
V3Number& V3Number::setQuad(vluint64_t value) {
    for (int i=0; i<words(); i++) m_value[i]=m_valueX[i] = 0;
    m_value[0] = value & VL_ULL(0xffffffff);
    m_value[1] = (value>>VL_ULL(32)) & VL_ULL(0xffffffff);
    return *this;
}
V3Number& V3Number::setLong(uint32_t value) {
    for (int i=0; i<words(); i++) m_value[i]=m_valueX[i] = 0;
    m_value[0] = value;
    return *this;
}
V3Number& V3Number::setSingleBits(char value) {
    for (int i=1/*upper*/; i<words(); i++) m_value[i]=m_valueX[i] = 0;
    m_value[0] = (value=='1'||value=='x'||value==1||value==3);
    m_valueX[0] = (value=='z'||value=='x'||value==2||value==3);
    return *this;
}

V3Number& V3Number::setAllBitsX() {
    for (int i=0; i<words(); i++) { m_value[i]=m_valueX[i] = ~0; }
    return *this;
}
V3Number& V3Number::setAllBitsZ() {
    for (int i=0; i<words(); i++) { m_value[i]=0; m_valueX[i] = ~0; }
    return *this;
}
V3Number& V3Number::setMask(int nbits) {
    setZero();
    for (int bit=0; bit<nbits; bit++) { setBit(bit,1); }
    return *this;
}

//======================================================================
// ACCESSORS - as strings

string V3Number::ascii(bool prefixed, bool cleanVerilog) const {
    ostringstream out;

    if (prefixed) {
	if (sized()) {
	    out<<width()<<"'";
	} else if (autoExtend() && !sized() && width()==1) {
	    out<<"'";
	    if (bitIs0(0)) out<<'0';
	    else if (bitIs1(0)) out<<'1';
	    else if (bitIsZ(0)) out<<'z';
	    else out<<'x';
	    return out.str();
	} else {
	    if (cleanVerilog) out<<"'";
	    else out<<"?"<<width()<<"?";
	}
	if (isSigned()) out<<"s";
    }

    bool binary = (isFourState()
#ifdef V3NUMBER_ASCII_BINARY
		   || 1
#endif
	);
    //out<<"-"<<hex<<m_value[0]<<"-";
    
    if (binary) {
	out<<"b";
	out<<displayed("%0b");
    }
    else {
	if (prefixed) out<<"h";
	// Always deal with 4 bits at once.  Note no 4-state, it's above.
	out<<displayed("%0h");
    }
    return out.str();
}

string V3Number::displayed(const string& vformat) const {
    string::const_iterator pos = vformat.begin();
    UASSERT(pos != vformat.end() && pos[0]=='%', "display with non format argument "<<*this);
    pos++;
    string fmtsize;
    for (; pos != vformat.end() && isdigit(pos[0]); pos++) {
	fmtsize += pos[0];
    }
    string str;
    char code = tolower(pos[0]);
    switch (code) {
    case 'b': {
	int bit = width()-1;
	if (fmtsize == "0") while (bit && bitIs0(bit)) bit--;
	for (; bit>=0; bit--) {
	    if (bitIs0(bit)) str+='0';
	    else if (bitIs1(bit)) str+='1';
	    else if (bitIsZ(bit)) str+='z';
	    else str+='x';
	}
	return str;
    }
    case 'o': {
	int bit = width()-1;
	if (fmtsize == "0") while (bit && bitIs0(bit)) bit--;
	while ((bit%3)!=2) bit++;
	for (; bit>0; bit -= 3) {
	    int v = bitsValue(bit-2, 3);
	    str += (char)('0'+v);
	}
	return str;
    }
    case 'h':
    case 'x': {
	int bit = width()-1;
	if (fmtsize == "0") while (bit && bitIs0(bit)) bit--;
	while ((bit%4)!=3) bit++;
	for (; bit>0; bit -= 4) {
	    int v = bitsValue(bit-3, 4);
	    if (v>=10) str += (char)('a'+v-10);
	    else str += (char)('0'+v);
	}
	return str;
    }
    case 'c': {
	if (this->width()>8) m_fileline->v3error("$display of char format of > 8 bit value");
	int v = bitsValue(0, 8);
	str += (char)(v);
	return str;
    }
    case 's': {
	// Spec says always drop leading zeros, this isn't quite right, we space pad.
	int bit=this->width()-1;
	bool start=true;
	while ((bit%8)!=7) bit++;
	for (; bit>=0; bit -= 8) {
	    int v = bitsValue(bit-7, 8);
	    if (!start || v) {
		str += (char)((v==0)?' ':v);
		start = false;	// Drop leading 0s
	    } else {
		if (fmtsize != "0") str += ' ';
	    }
	}
	return str;
    }
    case '~': // Signed decimal
    case 't':
    case 'd': { // Unsigned decimal
	bool issigned = (code == '~');
	if (fmtsize == "") {
	    double mantissabits = this->width() - (issigned?1:0);
	    double maxval = pow(2.0, mantissabits);
	    double dchars = log10(maxval)+1.0;
	    if (issigned) dchars++;  // space for sign
	    fmtsize = cvtToStr(int(dchars));
	}
	if (width() > 64) {
	    m_fileline->v3error("Unsupported: $display of dec format of > 64 bit results (use hex format instead)");
	    return "ERR";
	}
	if (issigned) {
	    str = cvtToStr(asSQuad());
	} else {
	    str = cvtToStr(asQuad());
	}
	int intfmtsize = atoi(fmtsize.c_str());
	while ((int)(str.length()) < intfmtsize) str = " "+str;
	return str;
    }
    default:
	m_fileline->v3fatalSrc("Unknown $display format code for number: %"<<pos[0]);
	return "ERR";
    }
}

//======================================================================
// ACCESSORS - as numbers

uint32_t V3Number::asInt() const {
    UASSERT(!isFourState(),"asInt with 4-state "<<*this);
    UASSERT((width()<33 || (width()<65 && m_value[1]==0)), "Value too wide "<<*this);
    return m_value[0];
}

vlsint32_t V3Number::asSInt() const {
    uint32_t v = asInt();
    uint32_t signExtend = (-(v & (1UL<<(width()-1))));
    uint32_t extended = v | signExtend;
    return (vlsint32_t)(extended);
}

vluint64_t V3Number::asQuad() const {
    UASSERT(!isFourState(),"asQuad with 4-state "<<*this);
    UASSERT(width()<65, "Value too wide "<<*this);
    if (width()<=32) return ((vluint64_t)(asInt()));
    return ((vluint64_t)m_value[1]<<VL_ULL(32)) | ((vluint64_t)m_value[0]);
}

vlsint64_t V3Number::asSQuad() const {
    vluint64_t v = asQuad();
    vluint64_t signExtend = (-(v & (VL_ULL(1)<<(width()-1))));
    vluint64_t extended = v | signExtend;
    return (vlsint64_t)(extended);
}

uint32_t V3Number::asHash() const {
    return m_value[0];
}

uint32_t V3Number::dataWord(int word) const {
    UASSERT(!isFourState(),"dataWord with 4-state "<<*this);
    return m_value[word];
}

bool V3Number::isEqZero() const {
    for (int i=0; i<words(); i++) {
	if (m_value[i] || m_valueX[i]) return false;
    }
    return true;
}
bool V3Number::isNeqZero() const {
    for (int i=0; i<words(); i++) {
	if (m_value[i] & ~m_valueX[i]) return true;
    }
    return false;
}
bool V3Number::isEqOne() const {
    if (m_value[0]!=1 || m_valueX[0]) return false;
    for (int i=1; i<words(); i++) {
	if (m_value[i] || m_valueX[i]) return false;
    }
    return true;
}
bool V3Number::isEqAllOnes(int optwidth) const {
    if (!optwidth) optwidth = width();
    for(int bit=0; bit<optwidth; bit++) {
	if (!bitIs1(bit)) return false;
    }
    return true;
}

int V3Number::minWidth() const {
    for(int bit=width()-1; bit>0; bit--) {
	if (!bitIs0(bit)) return bit+1;
    }
    return 1;	// one bit even if number is == 0
}

uint32_t V3Number::countOnes() const {
    int n=0;
    for(int bit=0; bit<this->width(); bit++) {
	if (bitIs1(bit)) n++; 
    }
    return n;
}

uint32_t V3Number::mostSetBitP1() const {
    for (int bit=this->width()-1; bit>=0; bit--) {
	if (bitIs1(bit)) return bit+1;
    }
    return 0;
}
//======================================================================

V3Number& V3Number::opBitsNonX (const V3Number& lhs) { // 0/1->1, X/Z->0
    // op i, L(lhs) bit return
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs0(bit) || lhs.bitIs1(bit))  { setBit(bit,1); }
    }
    return *this;
}
V3Number& V3Number::opBitsOne (const V3Number& lhs) { // 1->1, 0/X/Z->0
    // op i, L(lhs) bit return
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs1(bit))  { setBit(bit,1); }
    }
    return *this;
}
V3Number& V3Number::opBitsXZ (const V3Number& lhs) { // 0/1->1, X/Z->0
    // op i, L(lhs) bit return
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIsXZ(bit))  { setBit(bit,1); }
    }
    return *this;
}

//======================================================================
// Operators - Simple per-bit logical ops

V3Number& V3Number::opRedOr (const V3Number& lhs) {
    // op i, 1 bit return
    char outc = 0;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs1(bit)) return setSingleBits(1);
	else if (lhs.bitIs0(bit)) ;
	else outc = 'x';
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opRedAnd (const V3Number& lhs) {
    // op i, 1 bit return
    char outc = 1;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs0(bit)) return setSingleBits(0);
	else if (lhs.bitIs1(bit)) ;
	else outc = 'x';
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opRedXor (const V3Number& lhs) {
    // op i, 1 bit return
    char outc = 0;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs1(bit)) { if (outc==1) outc=0; else if (outc==0) outc=1; }
	else if (lhs.bitIs0(bit)) ;
	else outc = 'x';
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opRedXnor (const V3Number& lhs) {
    // op i, 1 bit return
    char outc = 1;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs1(bit)) { if (outc==1) outc=0; else if (outc==0) outc=1; }
	else if (lhs.bitIs0(bit)) ;
	else outc = 'x';
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opCountOnes (const V3Number& lhs) {
    if (lhs.isFourState()) return setAllBitsX();
    setZero();
    m_value[0] = lhs.countOnes();
    return *this;
}
V3Number& V3Number::opIsUnknown (const V3Number& lhs) {
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIsX(bit)) return setSingleBits(1);
    }
    return setSingleBits(0);
}
V3Number& V3Number::opOneHot (const V3Number& lhs) {
    if (lhs.isFourState()) return setAllBitsX();
    return setSingleBits(lhs.countOnes()==1);
}
V3Number& V3Number::opOneHot0 (const V3Number& lhs) {
    if (lhs.isFourState()) return setAllBitsX();
    return setSingleBits(lhs.countOnes()<=1);
}

V3Number& V3Number::opLogNot (const V3Number& lhs) {
    // op i, 1 bit return
    char outc = 1;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs1(bit)) { outc=0; goto last;}
	else if (lhs.bitIs0(bit)) ;
	else outc = 'x';
    }
  last:
    return setSingleBits(outc);
}

V3Number& V3Number::opNot (const V3Number& lhs) {
    // op i, L(lhs) bit return
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs0(bit))       { setBit(bit,1); }
	else if (lhs.bitIsXZ(bit)) { setBit(bit,'x'); }
    }
    return *this;
}

V3Number& V3Number::opAnd (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs1(bit) && rhs.bitIs1(bit))  { setBit(bit,1); }
	else if (lhs.bitIs0(bit) || rhs.bitIs0(bit)) ;  // 0
	else { setBit(bit,'x'); }
    }
    return *this;
}

V3Number& V3Number::opOr (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs1(bit) || rhs.bitIs1(bit))  { setBit(bit,1); }
	else if (lhs.bitIs0(bit) && rhs.bitIs0(bit)) ;  // 0
	else { setBit(bit,'x'); }
    }
    return *this;
}

V3Number& V3Number::opChangeXor (const V3Number& lhs, const V3Number& rhs) {
    // 32 bit result
    opEq(lhs,rhs);
    return *this;
}

V3Number& V3Number::opXor (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs1(bit) && rhs.bitIs0(bit))  { setBit(bit,1); }
	else if (lhs.bitIs0(bit) && rhs.bitIs1(bit))  { setBit(bit,1); }
	else if (lhs.bitIsXZ(bit) && rhs.bitIsXZ(bit)) { setBit(bit,'x'); }
	// else zero
    }
    return *this;
}

V3Number& V3Number::opXnor (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, careful need to X/Z extend.
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	if (lhs.bitIs1(bit) && rhs.bitIs1(bit))  { setBit(bit,1); }
	else if (lhs.bitIs0(bit) && rhs.bitIs0(bit))  { setBit(bit,1); }
	else if (lhs.bitIsXZ(bit) && rhs.bitIsXZ(bit)) { setBit(bit,'x'); }
	// else zero
    }
    return *this;
}

V3Number& V3Number::opConcat (const V3Number& lhs, const V3Number& rhs) {
    setZero();
    if (!lhs.sized()) m_fileline->v3error("Unsized constants not allowed in concatenations: "<<lhs);
    if (!rhs.sized()) m_fileline->v3error("Unsized constants not allowed in concatenations: "<<rhs);
    int obit = 0;
    for(int bit=0; bit<rhs.width(); bit++) {
	setBit(obit,rhs.bitIs(bit));
	obit++;
    }
    for(int bit=0; bit<lhs.width(); bit++) {
	setBit(obit,lhs.bitIs(bit));
	obit++;
    }
    return *this;
}

V3Number& V3Number::opRepl (const V3Number& lhs, const V3Number& rhs) {	// rhs is # of times to replicate
    // Hopefully the using routine has a error check too.
    if (!lhs.sized()) m_fileline->v3error("Unsized constants not allowed in concatenations: "<<lhs);
    return opRepl(lhs, rhs.asInt());
}

V3Number& V3Number::opRepl (const V3Number& lhs, uint32_t rhsval) {	// rhs is # of times to replicate
    // i op repl, L(i)*value(rhs) bit return
    setZero();
    if (rhsval>8192) m_fileline->v3fatal("More then a 8k bit replication is probably wrong: "<<rhsval);
    int obit = 0;
    for (unsigned times=0; times<rhsval; times++) {
	for(int bit=0; bit<lhs.width(); bit++) {
	    setBit(obit,lhs.bitIs(bit));
	    obit++;
	}
    }
    return *this;
}

V3Number& V3Number::opLogAnd (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation
    char loutc = 0;
    char routc = 0;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs1(bit)) { loutc=1; break; }
	if (lhs.bitIsXZ(bit) && loutc==0) { loutc='x'; }
    }
    for(int bit=0; bit<rhs.width(); bit++) {
	if (rhs.bitIs1(bit)) { routc=1; break; }
	if (rhs.bitIsXZ(bit) && routc==0) { routc='x'; }
    }
    char outc = 'x';
    if (routc==1 && loutc==1) outc=1;
    if (routc==0 || loutc==0) outc=0;
    return setSingleBits(outc);
}

V3Number& V3Number::opLogOr (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    char outc = 0;
    for(int bit=0; bit<lhs.width(); bit++) {
	if (lhs.bitIs1(bit)) { outc=1; goto last; }
	if (lhs.bitIsXZ(bit) && outc==0) { outc='x'; }
    }
    for(int bit=0; bit<rhs.width(); bit++) {
	if (rhs.bitIs1(bit)) { outc=1; goto last; }
	if (rhs.bitIsXZ(bit) && outc==0) { outc='x'; }
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opEq (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    char outc = 1;
    for (int bit=0; bit<max(lhs.width(),rhs.width()); bit++) {
	if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) { outc=0; goto last; }
	if (lhs.bitIs0(bit) && rhs.bitIs1(bit)) { outc=0; goto last; }
	if (lhs.bitIsXZ(bit)) { outc='x'; }
	if (rhs.bitIsXZ(bit)) { outc='x'; }
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opNeq (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    char outc = 0;
    for (int bit=0; bit<max(lhs.width(),rhs.width()); bit++) {
	if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) { outc=1; goto last; }
	if (lhs.bitIs0(bit) && rhs.bitIs1(bit)) { outc=1; goto last; }
	if (lhs.bitIsXZ(bit)) { outc='x'; }
	if (rhs.bitIsXZ(bit)) { outc='x'; }
    }
last:
    return setSingleBits(outc);
}

bool V3Number::isCaseEq (const V3Number& rhs) const {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    if (this->width() != rhs.width()) return false;
    for (int bit=0; bit<max(this->width(),rhs.width()); bit++) {
	if (this->bitIs(bit) != rhs.bitIs(bit)) { return false; }
    }
    return true;
}

V3Number& V3Number::opCaseEq (const V3Number& lhs, const V3Number& rhs) {
    return setSingleBits(lhs.isCaseEq(rhs) ? 1:0);
}

V3Number& V3Number::opCaseNeq (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    char outc = 0;
    for (int bit=0; bit<max(lhs.width(),rhs.width()); bit++) {
	if (lhs.bitIs(bit) != rhs.bitIs(bit)) { outc=1; goto last; }
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opWildEq (const V3Number& lhs, const V3Number& rhs) {
    char outc = 1;
    for (int bit=0; bit<max(lhs.width(),rhs.width()); bit++) {
	if (!rhs.bitIsXZ(bit)
	    && lhs.bitIs(bit) != rhs.bitIs(bit)) { outc=0; goto last; }
	if (lhs.bitIsXZ(bit)) outc='x';
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opWildNeq (const V3Number& lhs, const V3Number& rhs) {
    char outc = 0;
    for (int bit=0; bit<max(lhs.width(),rhs.width()); bit++) {
	if (!rhs.bitIsXZ(bit) 
	    && lhs.bitIs(bit) != rhs.bitIs(bit)) { outc=1; goto last; }
	if (lhs.bitIsXZ(bit)) outc='x';
    }
last:
    return setSingleBits(outc);
}

V3Number& V3Number::opGt (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    char outc = 0;
    for (int bit=0; bit<max(lhs.width(),rhs.width()); bit++) {
	if (lhs.bitIs1(bit) && rhs.bitIs0(bit)) { outc=1; }
	if (rhs.bitIs1(bit) && lhs.bitIs0(bit)) { outc=0; }
	if (lhs.bitIsXZ(bit)) { outc='x'; }
	if (rhs.bitIsXZ(bit)) { outc='x'; }
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opGtS (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    char outc = 0;
    {
	int mbit=max(lhs.width()-1,rhs.width()-1);
	if (lhs.bitIsXZ(mbit)) { outc='x'; }
	else if (rhs.bitIsXZ(mbit)) { outc='x'; }
	else if (lhs.bitIs0(mbit)       && rhs.bitIs1Extend(mbit)) { outc=1; } // + > -
	else if (lhs.bitIs1Extend(mbit) && rhs.bitIs0(mbit))       { outc=0; } // - !> +
	else {
	    // both positive or negative, normal >
	    for (int bit=0; bit<max(lhs.width()-1,rhs.width()-1); bit++) {
		if (lhs.bitIs1Extend(bit) && rhs.bitIs0(bit)) { outc=1; }
		if (rhs.bitIs1Extend(bit) && lhs.bitIs0(bit)) { outc=0; }
		if (lhs.bitIsXZ(bit)) { outc='x'; }
		if (rhs.bitIsXZ(bit)) { outc='x'; }
	    }
	}
    }
    return setSingleBits(outc);
}

V3Number& V3Number::opGte (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    V3Number& eq = opEq (lhs,rhs);
    if (eq.isNeqZero()) return eq; // Return true
    return opGt (lhs,rhs);
}

V3Number& V3Number::opGteS (const V3Number& lhs, const V3Number& rhs) {
    // i op j, 1 bit return, max(L(lhs),L(rhs)) calculation, careful need to X/Z extend.
    V3Number& eq = opEq (lhs,rhs);
    if (eq.isNeqZero()) return eq; // Return true
    return opGtS (lhs,rhs);
}

V3Number& V3Number::opLt (const V3Number& lhs, const V3Number& rhs) {
    return opGt(rhs,lhs);
}
V3Number& V3Number::opLte (const V3Number& lhs, const V3Number& rhs) {
    return opGte(rhs,lhs);
}
V3Number& V3Number::opLtS (const V3Number& lhs, const V3Number& rhs) {
    return opGtS(rhs,lhs);
}
V3Number& V3Number::opLteS (const V3Number& lhs, const V3Number& rhs) {
    return opGteS(rhs,lhs);
}

V3Number& V3Number::opShiftR (const V3Number& lhs, const V3Number& rhs) {
    // L(lhs) bit return
    if (rhs.isFourState()) return setAllBitsX();
    setZero();
    uint32_t rhsval = rhs.asInt();
    for (int bit=0; bit<this->width(); bit++) {
	setBit(bit,lhs.bitIs(bit + rhsval));
    }
    return *this;
}

V3Number& V3Number::opShiftRS (const V3Number& lhs, const V3Number& rhs) {
    // L(lhs) bit return
    // The spec says a unsigned >>> still acts as a normal >>.
    // We presume it is signed; as that's V3Signed's job to convert to opShiftR
    if (rhs.isFourState()) return setAllBitsX();
    setZero();
    uint32_t rhsval = rhs.asInt();
    for (int bit=0; bit<this->width(); bit++) {
	setBit(bit,lhs.bitIsExtend(bit + rhsval));
    }
    return *this;
}

V3Number& V3Number::opShiftL (const V3Number& lhs, const V3Number& rhs) {
    // L(lhs) bit return
    if (rhs.isFourState()) return setAllBitsX();
    uint32_t rhsval = rhs.asInt();
    setZero();
    for (int bit=0; bit<this->width(); bit++) {
	if (bit >= (int)rhsval) {
	    setBit(bit,lhs.bitIs(bit - rhsval));
	}
    }
    return *this;
}

//======================================================================
// Ops - Arithmetic

V3Number& V3Number::opUnaryMin (const V3Number& lhs) {
    // op i, L(lhs) bit return
    if (lhs.isFourState()) return setAllBitsX();
    V3Number notlhs (lhs.m_fileline, width());
    notlhs.opNot(lhs);
    V3Number one (lhs.m_fileline, width(), 1);
    opAdd(notlhs,one);
    return *this;
}
V3Number& V3Number::opAdd (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    setZero();
    // Addem
    int carry=0;
    for (int bit=0; bit<this->width(); bit++) {
	int sum = ((lhs.bitIs1(bit)?1:0) + (rhs.bitIs1(bit)?1:0) + carry);
	if (sum & 1) {
	    setBit(bit,1);
	}
	carry = (sum >= 2);
    }
    return *this;
}
V3Number& V3Number::opSub (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    V3Number negrhs (rhs.m_fileline, rhs.width());
    negrhs.opUnaryMin(rhs);
    return opAdd(lhs, negrhs);
}
V3Number& V3Number::opMul (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    setZero();
    if (width() <= 64) {
	setQuad(lhs.asQuad() * rhs.asQuad());
	opCleanThis();   // Mult produces extra bits in result
    } else {
	for (int lword=0; lword<lhs.words(); lword++) {
	    for (int rword=0; rword<rhs.words(); rword++) {
		vluint64_t mul = (vluint64_t)(lhs.m_value[lword]) * (vluint64_t)(rhs.m_value[rword]);
		for (int qword=lword+rword; qword<this->words(); qword++) {
		    mul += (vluint64_t)(m_value[qword]);
		    m_value[qword] = (mul & VL_ULL(0xffffffff));
		    mul = (mul >> VL_ULL(32)) & VL_ULL(0xffffffff);
		}
	    }
	}
	opCleanThis();   // Mult produces extra bits in result
    }
    return *this;
}
V3Number& V3Number::opMulS (const V3Number& lhs, const V3Number& rhs) {
    // Signed multiply
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    V3Number lhsNoSign = lhs;  if (lhs.isNegative()) lhsNoSign.opUnaryMin(lhs);
    V3Number rhsNoSign = rhs;  if (rhs.isNegative()) rhsNoSign.opUnaryMin(rhs);
    V3Number qNoSign = opMul(lhsNoSign,rhsNoSign);
    if (lhs.isNegative() && !rhs.isNegative()
	|| !lhs.isNegative() && rhs.isNegative()) {
	opUnaryMin(qNoSign);
    } else {
	opAssign(qNoSign);
    }
    return *this;
}
V3Number& V3Number::opDiv (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsX();
    if (lhs.width()>64) m_fileline->v3fatalSrc("Unsupported: Large / math not implemented yet: "<<*this);
    if (rhs.width()>64) m_fileline->v3fatalSrc("Unsupported: Large / math not implemented yet: "<<*this);
    setQuad(lhs.asQuad() / rhs.asQuad());
    return *this;
}
V3Number& V3Number::opDivS (const V3Number& lhs, const V3Number& rhs) {
    // Signed divide
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsX();
    V3Number lhsNoSign = lhs;  if (lhs.isNegative()) lhsNoSign.opUnaryMin(lhs);
    V3Number rhsNoSign = rhs;  if (rhs.isNegative()) rhsNoSign.opUnaryMin(rhs);
    V3Number qNoSign = opDiv(lhsNoSign,rhsNoSign);
    if (lhs.isNegative() && !rhs.isNegative()
	|| !lhs.isNegative() && rhs.isNegative()) {
	opUnaryMin(qNoSign);
    } else {
	opAssign(qNoSign);
    }
    return *this;
}
V3Number& V3Number::opModDiv (const V3Number& lhs, const V3Number& rhs) {
    // i op j, max(L(lhs),L(rhs)) bit return, if any 4-state, 4-state return
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsX();
    if (lhs.width()>64) m_fileline->v3fatalSrc("Unsupported: Large % math not implemented yet: "<<*this);
    if (rhs.width()>64) m_fileline->v3fatalSrc("Unsupported: Large % math not implemented yet: "<<*this);
    setQuad(lhs.asQuad() % rhs.asQuad());
    return *this;
}
V3Number& V3Number::opModDivS (const V3Number& lhs, const V3Number& rhs) {
    // Signed moddiv
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (rhs.isEqZero()) return setAllBitsX();
    V3Number lhsNoSign = lhs;  if (lhs.isNegative()) lhsNoSign.opUnaryMin(lhs);
    V3Number rhsNoSign = rhs;  if (rhs.isNegative()) rhsNoSign.opUnaryMin(rhs);
    V3Number qNoSign = opModDiv(lhsNoSign,rhsNoSign);
    if (lhs.isNegative()) {	// Just lhs' sign  (*DIFFERENT FROM PERL, which uses rhs sign*)
	opUnaryMin(qNoSign);
    } else {
	opAssign(qNoSign);
    }
    return *this;
}
V3Number& V3Number::opPow (const V3Number& lhs, const V3Number& rhs) {
    // L(i) bit return, if any 4-state, 4-state return
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (lhs.isEqZero()) return setZero();
    // We may want to special case when the lhs is 2, so we can get larger outputs
    if (lhs.width()>64) m_fileline->v3fatalSrc("Unsupported: Large >64bit ** math not implemented yet: "<<*this);
    if (rhs.width()>64) m_fileline->v3fatalSrc("Unsupported: Large >64bit ** math not implemented yet: "<<*this);
    setZero();
    m_value[0] = 1;
    V3Number power (lhs.m_fileline, width());  power.opAssign(lhs);
    for (int bit=0; bit<rhs.width(); bit++) {
	if (bit>0) {  // power = power*power
	    V3Number lastPower (lhs.m_fileline, width());  lastPower.opAssign(power);
	    power.opMul(lastPower, lastPower);
	}
	if (rhs.bitIs1(bit)) {  // out *= power
	    V3Number lastOut (lhs.m_fileline, width()); lastOut.opAssign(*this);
	    this->opMul(lastOut, power);
	    //UINFO(0, "pow "<<lhs<<" "<<rhs<<" b"<<bit<<" pow="<<power<<" now="<<*this<<endl);
	}
    }
    return *this;
}
V3Number& V3Number::opPowS (const V3Number& lhs, const V3Number& rhs) {
    // Signed multiply
    if (lhs.isFourState() || rhs.isFourState()) return setAllBitsX();
    if (lhs.isEqZero() && rhs.isNegative()) return setAllBitsX();  // Per spec
    if (!lhs.isNegative() && !rhs.isNegative()) return opPow(lhs,rhs);
    //if (lhs.isNegative() || rhs.isNonIntegral()) return setAllBitsX();  // Illegal pow() call
    m_fileline->v3fatalSrc("Unsupported: Power (**) operator with negative numbers: "<<*this);
    return setAllBitsX();
}

V3Number& V3Number::opAssign (const V3Number& lhs) {
    // Note may be a width change during the assign
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	setBit(bit,lhs.bitIs(bit));
    }
    return *this;
}

V3Number& V3Number::opExtendS (const V3Number& lhs) {
    // Note may be a width change during the sign extension
    setZero();
    for(int bit=0; bit<this->width(); bit++) {
	setBit(bit,lhs.bitIsExtend(bit));
    }
    return *this;
}

V3Number& V3Number::opClean (const V3Number& lhs, uint32_t bits) {
    return opRange(lhs, bits-1, 0);
}

void V3Number::opCleanThis() {
    // Clean in place number
    if (uint32_t okbits = (width() & 31)) {
	m_value[words()-1] &= ((1UL<<okbits)-1);
    }
}

V3Number& V3Number::opRange (const V3Number& lhs, const V3Number& msb, const V3Number& lsb) {
    if (lsb.isFourState() || msb.isFourState()) return setAllBitsX();
    return opRange(lhs, msb.asInt(), lsb.asInt());
}

V3Number& V3Number::opRange (const V3Number& lhs, uint32_t msbval, uint32_t lsbval) {
    setZero();
    int ibit=lsbval;
    for(int bit=0; bit<this->width(); bit++) {
	if (ibit>=0 && ibit<lhs.width()
	    && ibit<=(int)msbval) {
	    setBit(bit,lhs.bitIs(ibit));
	} else {
	    setBit(bit,'x');
	}
	ibit++;
    }
    //UINFO(0,"RANGE "<<lhs<<" "<<msb<<" "<<lsb<<" = "<<*this<<endl);
    return *this;
}

V3Number& V3Number::opCond  (const V3Number& lhs, const V3Number& if1s, const V3Number& if0s) {
    V3Number lhstrue (lhs.m_fileline);  lhstrue.opRedOr(lhs);
    if (lhstrue.bitIs0(0)) {
	this->opAssign(if0s);
    }
    else if (lhstrue.bitIs1(0)) {
	this->opAssign(if1s);
    }
    else { // select is "X/Z"
	setZero();
	for(int bit=0; bit<this->width(); bit++) {
	    if (if0s.bitIs1(bit) && if1s.bitIs1(bit))  { setBit(bit,1); }
	    else if (if0s.bitIs0(bit) && if1s.bitIs0(bit))  { setBit(bit,0); }
	    else setBit(bit,'x');
	}
    }
    return *this;
}
