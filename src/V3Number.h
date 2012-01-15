// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Large 4-state numbers
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3NUMBER_H_
#define _V3NUMBER_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include <vector>

#include "V3Error.h"

//============================================================================

class V3Number {
    // Large 4-state number handling
    int		m_width;	// Width as specified/calculated.
    bool	m_sized:1;	// True if the user specified the width, else we track it.
    bool	m_signed:1;	// True if signed value
    bool	m_double:1;	// True if double real value
    bool	m_fromString:1;	// True if from string
    bool	m_autoExtend:1;	// True if SystemVerilog extend-to-any-width
    FileLine*	m_fileline;
    vector<uint32_t>	m_value;	// The Value, with bit 0 being in bit 0 of this vector (unless X/Z)
    vector<uint32_t>	m_valueX;	// Each bit is true if it's X or Z, 10=z, 11=x
    // METHODS
    V3Number& setSingleBits(char value);
    void opCleanThis();
public:
    FileLine*	fileline() const { return m_fileline; }
    void	fileline(FileLine* fl) { m_fileline=fl; }
    V3Number& setZero();
    V3Number& setQuad(vluint64_t value);
    V3Number& setLong(uint32_t value);
    V3Number& setLongS(vlsint32_t value);
    V3Number& setDouble(double value);
    void setBit (int bit, char value) {		// Note must be pre-zeroed!
	if (bit>=m_width) return;
	if (value=='0'||value==0)                       m_value [bit/32] &= ~(1UL<<(bit&31));
	else {
	    if (value=='1'||value=='x'||value==1||value==3) m_value [bit/32] |= (1UL<<(bit&31));
	    if (value=='z'||value=='x'||value==2||value==3) m_valueX[bit/32] |= (1UL<<(bit&31));
	}
    }
private:
    char bitIs	(int bit) const {
	if (bit>=m_width) {
	    bit = m_width-1;
	    // We never sign extend
	    return ( "00zx"[(((m_value[bit/32] & (1UL<<(bit&31)))?1:0)
			     | ((m_valueX[bit/32] & (1UL<<(bit&31)))?2:0))] );
	}
	return ( "01zx"[(((m_value[bit/32] & (1UL<<(bit&31)))?1:0)
			 | ((m_valueX[bit/32] & (1UL<<(bit&31)))?2:0))] ); }
    char bitIsExtend (int bit) const {
	if (bit>=m_width) {
	    bit = m_width-1;
	    // We do sign extend
	    return ( "01zx"[(((m_value[bit/32] & (1UL<<(bit&31)))?1:0)
			     | ((m_valueX[bit/32] & (1UL<<(bit&31)))?2:0))] );
	}
	return ( "01zx"[(((m_value[bit/32] & (1UL<<(bit&31)))?1:0)
			 | ((m_valueX[bit/32] & (1UL<<(bit&31)))?2:0))] ); }
    bool bitIs0	(int bit) const {
	if (bit>=m_width) return !bitIsXZ(m_width-1);
	return ( (m_value[bit/32] & (1UL<<(bit&31)))==0 && !(m_valueX[bit/32] & (1UL<<(bit&31))) ); }
    bool bitIs1	(int bit) const {
	if (bit>=m_width) return false;
	return ( (m_value[bit/32] & (1UL<<(bit&31))) && !(m_valueX[bit/32] & (1UL<<(bit&31))) ); }
    bool bitIs1Extend (int bit) const {
	if (bit>=m_width) return bitIs1Extend(m_width-1);
	return ( (m_value[bit/32] & (1UL<<(bit&31))) && !(m_valueX[bit/32] & (1UL<<(bit&31))) ); }
    bool bitIsX (int bit) const {
	if (bit>=m_width) return bitIsZ(m_width-1);
	return ( (m_value[bit/32] & (1UL<<(bit&31))) && (m_valueX[bit/32] & (1UL<<(bit&31))) ); }
    bool bitIsXZ(int bit) const {
	if (bit>=m_width) return bitIsXZ(m_width-1);
	return ( (m_valueX[bit/32] & (1UL<<(bit&31))) && 1);
    }
    bool bitIsZ (int bit) const {
	if (bit>=m_width) return bitIsZ(m_width-1);
	return ( (~m_value[bit/32] & (1UL<<(bit&31))) && (m_valueX[bit/32] & (1UL<<(bit&31))) ); }
    uint32_t bitsValue(int lsb, int nbits) const {
	uint32_t v=0;
	for (int bitn=0; bitn<nbits; bitn++) { v |= (bitIs1(lsb+bitn)<<bitn); }
	return v;
    }

    int words() const { return ((width()+31)/32); }

    V3Number& opModDivGuts(const V3Number& lhs, const V3Number& rhs, bool is_modulus);

public:
    class VerilogString {};	// for creator type-overload selection
    // CONSTRUCTORS
    V3Number(FileLine* fileline) { init(fileline, 1); }
    V3Number(FileLine* fileline, int width) { init(fileline, width); }  // 0=unsized
    V3Number(FileLine* fileline, int width, uint32_t value) { init(fileline, width); m_value[0]=value; }
    V3Number(FileLine* fileline, const char* source);	// Create from a verilog 32'hxxxx number.
    V3Number(VerilogString, FileLine* fileline, const string& vvalue);

private:
    void init(FileLine* fileline, int swidth) {
	m_fileline = fileline;
	m_signed = false;
	m_double = false;
	m_autoExtend = false;
	m_fromString = false;
	width(swidth);
	for (int i=0; i<words(); i++) m_value[i]=m_valueX[i] = 0;
    }
public:
    void width(int width, bool sized=true) {
	// Set width.  Only set m_width here, as we need to tweak vector size
	if (width) { m_sized = sized; m_width=width; }
	else { m_sized = false; m_width=1; }
	if (VL_UNLIKELY(m_value.size() < (unsigned)(words()+1))) {
	    m_value.resize(words()+1);
	    m_valueX.resize(words()+1);
	}
    }

    // SETTERS
    V3Number& setAllBitsX();
    V3Number& setAllBitsZ();
    V3Number& setAllBits0();
    V3Number& setAllBits1();
    V3Number& setMask(int nbits);  // IE if nbits=1, then 0b1, if 2->0b11, if 3->0b111 etc

    // ACCESSORS
    string ascii(bool prefixed=true, bool cleanVerilog=false) const;
    string displayed(const string& format) const;
    static bool displayedFmtLegal(char format);  // Is this a valid format letter?
    int width() const { return m_width; }
    int widthMin() const;	// Minimum width that can represent this number (~== log2(num)+1)
    bool sized() const { return m_sized; }
    bool autoExtend() const { return m_autoExtend; }
    bool isFromString() const { return m_fromString; }
    bool isSigned() const { return m_signed; }	// Only correct for parsing of numbers from strings, otherwise not used (use AstConst::isSigned())
    bool isDouble() const { return m_double; }	// Only correct for parsing of numbers from strings, otherwise not used (use AstConst::isSigned())
    bool isNegative() const { return bitIs1(width()-1); }
    bool isFourState() const { for (int i=0;i<words();i++) {if (m_valueX[i]) return true;} return false; }
    bool hasZ() const { for(int i=0;i<words();i++) {if((~m_value[i]) & m_valueX[i]) return true;} return false;}
    bool isAllZ() const { for(int i=0;i<width();i++) { if(!bitIsZ(i)){return false;} } return true; }
    bool isEqZero() const;
    bool isNeqZero() const;
    bool isBitsZero(int msb, int lsb) const;
    bool isEqOne() const;
    bool isEqAllOnes(int optwidth=0) const;
    bool isCaseEq(const V3Number& rhsp) const;  // operator==
    bool isLt(const V3Number& rhsp) const;  // operator<
    void isSigned(bool ssigned) { m_signed=ssigned; }
    bool isUnknown() const;
    uint32_t toUInt() const;
    vlsint32_t toSInt() const;
    vluint64_t toUQuad() const;
    vlsint64_t toSQuad() const;
    string toString() const;
    double toDouble() const;
    uint32_t toHash() const;
    uint32_t dataWord(int word) const;
    uint32_t countOnes() const;
    uint32_t mostSetBitP1() const;	// Highest bit set plus one, IE for 16 return 5, for 0 return 0.

    // Operators
    bool operator<(const V3Number& rhs) const { return isLt(rhs); }

    // STATICS
    static int log2b(uint32_t num);

    typedef V3Number& (*UniopFuncp)(V3Number&);
    typedef V3Number& (*BiopFuncp) (V3Number&, V3Number&);

    // MATH
    // "this" is the output, as we need the output width before some computations
    V3Number& isTrue	(const V3Number& lhs);
    V3Number& opBitsNonX(const V3Number& lhs); // 0/1->1, X/Z->0
    V3Number& opBitsOne	(const V3Number& lhs); // 1->1, 0/X/Z->0
    V3Number& opBitsXZ	(const V3Number& lhs); // 0/1->0, X/Z->1
    V3Number& opBitsZ	(const V3Number& lhs); // Z->1, 0/1/X->0
    V3Number& opBitsNonZ(const V3Number& lhs); // Z->0, 0/1/X->1
    //
    V3Number& opAssign	(const V3Number& lhs);
    V3Number& opExtendS	(const V3Number& lhs); // Sign extension
    V3Number& opRedOr 	(const V3Number& lhs);
    V3Number& opRedAnd	(const V3Number& lhs);
    V3Number& opRedXor	(const V3Number& lhs);
    V3Number& opRedXnor	(const V3Number& lhs);
    V3Number& opCountOnes(const V3Number& lhs);
    V3Number& opIsUnknown(const V3Number& lhs);
    V3Number& opOneHot	(const V3Number& lhs);
    V3Number& opOneHot0	(const V3Number& lhs);
    V3Number& opCLog2	(const V3Number& lhs);
    V3Number& opClean	(const V3Number& lhs, uint32_t bits);
    V3Number& opConcat	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opRepl	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opRepl	(const V3Number& lhs, uint32_t rhs);
    V3Number& opSel	(const V3Number& lhs, const V3Number& rhs, const V3Number& ths);
    V3Number& opSel	(const V3Number& lhs, uint32_t rhs, uint32_t ths);
    V3Number& opCond	(const V3Number& lhs, const V3Number& rhs, const V3Number& ths);
    V3Number& opCaseEq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opCaseNeq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opWildEq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opWildNeq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opBufIf1	(const V3Number& lhs, const V3Number& rhs);
    // "standard" math
    V3Number& opNot	(const V3Number& lhs);
    V3Number& opLogNot	(const V3Number& lhs);
    V3Number& opLogAnd	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLogOr	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opAbsS    (const V3Number& lhs);
    V3Number& opNegate	(const V3Number& lhs);
    V3Number& opAdd	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opSub	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opMul	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opMulS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opDiv	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opDivS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opModDiv	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opModDivS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opPow	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opPowS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opAnd	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opChangeXor(const V3Number& lhs, const V3Number& rhs);
    V3Number& opXor	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opXnor	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opOr	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opRotR	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opRotL	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opShiftR	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opShiftRS	(const V3Number& lhs, const V3Number& rhs); // Arithmetic w/carry
    V3Number& opShiftL	(const V3Number& lhs, const V3Number& rhs);
    // Comparisons
    V3Number& opEq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opNeq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGt	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGtS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opGte	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGteS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opLt	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLtS	(const V3Number& lhs, const V3Number& rhs); // Signed
    V3Number& opLte	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLteS	(const V3Number& lhs, const V3Number& rhs); // Signed

    // "D" - double (aka real) math
    V3Number& opIToRD	(const V3Number& lhs);
    V3Number& opRToIS	(const V3Number& lhs);
    V3Number& opRToIRoundS (const V3Number& lhs);
    V3Number& opRealToBits (const V3Number& lhs);
    V3Number& opBitsToRealD(const V3Number& lhs);
    V3Number& opNegateD    (const V3Number& lhs);
    V3Number& opAddD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opSubD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opMulD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opDivD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opPowD	(const V3Number& lhs, const V3Number& rhs);
    // Comparisons
    V3Number& opEqD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opNeqD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGtD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opGteD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLtD	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLteD	(const V3Number& lhs, const V3Number& rhs);
};
inline ostream& operator<<(ostream& os, V3Number rhs) { return os<<rhs.ascii(); }

#endif // Guard
