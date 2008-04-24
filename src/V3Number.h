// $Id$ //-*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Large 4-state numbers
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
    bool	m_autoExtend:1;	// True if SystemVerilog extend-to-any-width
    FileLine*	m_fileline;
    vector<uint32_t>	m_value;	// The Value, with bit 0 being in bit 0 of this vector (unless X/Z)
    vector<uint32_t>	m_valueX;	// Each bit is true if it's X or Z, 10=z, 11=x
    // METHODS
    void init(FileLine* fileline, int width);
    V3Number& setZero();
    V3Number& setSingleBits(char value);
    void opCleanThis();
public:
    FileLine*	fileline() const { return m_fileline; }
    void	fileline(FileLine* fl) { m_fileline=fl; }
    V3Number& setQuad(vluint64_t value);
    V3Number& setLong(uint32_t value);
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
	return ( (m_valueX[bit/32] & (1UL<<(bit&31))) );
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

public:
    class VerilogString {};	// for creator type-overload selection
    // CONSTRUCTORS
    V3Number(FileLine* fileline) { init(fileline, 1); }
    V3Number(FileLine* fileline, int width) { init(fileline, width); };  // 0=unsized
    V3Number(FileLine* fileline, int width, uint32_t value) { init(fileline, width); m_value[0]=value; }
    V3Number(FileLine* fileline, const char* source);	// Create from a verilog 32'hxxxx number.
    V3Number(VerilogString, FileLine* fileline, const string& vvalue);

    // SETTERS
    V3Number& setAllBitsX();
    V3Number& setAllBitsZ();
    V3Number& setMask(int nbits);  // IE if nbits=1, then 0b1, if 2->0b11, if 3->0b111 etc

    // ACCESSORS
    string ascii(bool prefixed=true, bool cleanVerilog=false) const;
    string displayed(const string& format) const;
    int width() const { return m_width; }
    int minWidth() const;	// Minimum width that can represent this number (~== log2(num)+1)
    bool sized() const { return m_sized; }
    bool autoExtend() const { return m_autoExtend; }
    bool isSigned() const { return m_signed; }	// Only correct for parsing of numbers from strings, otherwise not used (use AstConst::isSigned())
    bool isNegative() const { return bitIs1(width()-1); }
    bool isFourState() const { for (int i=0;i<words();i++) {if (m_valueX[i]) return true;} return false; }
    bool isEqZero() const;
    bool isNeqZero() const;
    bool isEqOne() const;
    bool isEqAllOnes(int optwidth=0) const;
    bool isCaseEq(const V3Number& rhsp) const;  // operator==
    void width(int width, bool sized=true);
    void isSigned(bool ssigned) { m_signed=ssigned; }
    uint32_t asInt() const;
    vlsint32_t asSInt() const;
    vluint64_t asQuad() const;
    vlsint64_t asSQuad() const;
    uint32_t asHash() const;
    uint32_t dataWord(int word) const;
    uint32_t countOnes() const;
    uint32_t mostSetBitP1() const;	// Highest bit set plus one, IE for 16 return 5, for 0 return 0.

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
    V3Number& opRange	(const V3Number& lhs, const V3Number& rhs, const V3Number& ths);
    V3Number& opRange	(const V3Number& lhs, uint32_t rhs, uint32_t ths);
    V3Number& opCond	(const V3Number& lhs, const V3Number& rhs, const V3Number& ths);
    V3Number& opCaseEq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opCaseNeq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opWildEq	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opWildNeq	(const V3Number& lhs, const V3Number& rhs);
    // "standard" math
    V3Number& opNot	(const V3Number& lhs);
    V3Number& opLogNot	(const V3Number& lhs);
    V3Number& opLogAnd	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opLogOr	(const V3Number& lhs, const V3Number& rhs);
    V3Number& opUnaryMin(const V3Number& lhs);
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

};
inline ostream& operator<<(ostream& os, V3Number rhs) { return os<<rhs.ascii(); }

#endif // Guard
