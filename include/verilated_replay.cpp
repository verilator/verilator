// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2020 by Todd Strader. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: Common functions for replay tool
///
///     See verilator_replay
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#include "verilated_replay.h"
#define QUOTE(x) #x
#define MAKE_HEADER(x) QUOTE(x.h)
#include MAKE_HEADER(VM_PREFIX)

// TODO -- collapse into constructor?
int VerilatedReplay::init(std::string scope) {
    openFst(m_fstName);
    search(scope);
    m_time = fstReaderGetStartTime(m_fstp);
    // TODO -- use FST timescale
    m_simTime = m_time;

    for (VarMap::iterator it = m_inputs.begin(); it != m_inputs.end();
         ++it) {
        VL_PRINTF("%s = %d\n", it->second.fullName.c_str(), it->first);
        fstReaderSetFacProcessMask(m_fstp, it->first);
        m_signals[it->first] = FstSignal(it->second.hier.u.var.length,
                        reinterpret_cast<VM_PREFIX*>(m_modp)->??);
    }

    createMod();

    return 0;
}

VerilatedReplay::~VerilatedReplay() {
    fstReaderClose(m_fstp);
#if VM_TRACE
    if (m_tfp) m_tfp->close();
#endif
    delete(m_modp);
}

//int VerilatedReplay::addInput(const std::string& signalName, void* dutSignal, unsigned bits) {
//    for (std::vector<VCDSignal*>::iterator it = m_scopep->signals.begin();
//         it != m_scopep->signals.end(); ++it) {
//        if (signalName == (*it)->reference) {
//            VerilatedReplaySignal* signalp = new VerilatedReplaySignal;
//            signalp->dutSignal = dutSignal;
//            signalp->bits = bits;
//            signalp->hash = (*it)->hash;
//
//            if ((*it)->size != bits) {
//                VL_PRINTF("Error size mismatch on %s: trace=%d design=%d\n",
//                          signalName.c_str(), (*it)->size, bits);
//                return -1;
//            }
//
//            if ((*it)->type != VCD_VAR_REG && (*it)->type != VCD_VAR_WIRE) {
//                VL_PRINTF("Error unsupported signal type on %s\n", signalName.c_str());
//                return -1;
//            }
//
//            m_inputs.push_back(signalp);
//            return 0;
//        }
//    }
//    VL_PRINTF("Error finding signal (%s)\n", signalName.c_str());
//    return -1;
//}
//
//void VerilatedReplay::copySignal(uint8_t* signal, VCDValue* valuep) {
//    VCDValueType type = valuep->get_type();
//    switch(type) {
//        case VCD_SCALAR: {
//            copySignalBit(signal, 0, valuep->get_value_bit());
//            break;
//        }
//        case VCD_VECTOR: {
//            VCDBitVector* bitVector = valuep->get_value_vector();
//            unsigned length = bitVector->size();
//            for (int i = 0; i < length; ++i) {
//                copySignalBit(signal, i, bitVector->at(length - i - 1));
//            }
//            break;
//        }
//        default: {
//            VL_PRINTF("Error unsupported VCD value type");
//            exit(-1);
//        }
//    }
//}
//
//void VerilatedReplay::copySignalBit(uint8_t* signal, unsigned offset, VCDBit bit) {
//    unsigned byte = offset / 8;
//    unsigned byteOffset = offset % 8;
//    // TODO - more efficient byte copying
//    signal[byte] &= ~(0x1 << byteOffset);
//    // TODO - x's and z's?
//    signal[byte] |= (bit == VCD_1 ? 0x1 : 0x0) << byteOffset;
//}

int VerilatedReplay::replay() {
    // TODO -- lockless ring buffer for separate reader/replay threads
    // TODO -- should I be using fstReaderIterBlocks instead? (only one CB)
    // It appears that 0 is the error return code
    if (fstReaderIterBlocks2(m_fstp, &VerilatedReplay::fstCallback,
                             &VerilatedReplay::fstCallbackVarlen, this, NULL) == 0) {
        VL_PRINTF("Error iterating FST\n");
        exit(-1);
    }

    // One final eval + trace since we only eval on time changes
    eval();
    trace();
    final();

    return 0;
}

void VerilatedReplay::fstCb(uint64_t time, fstHandle facidx,
                            const unsigned char* valuep, uint32_t len) {
    // Watch for new time steps and eval before we start working on the new time
    if (m_time != time) {
        eval();
        trace();
        m_time = time;
        // TODO -- use FST timescale
        m_simTime = m_time;
    }

    // TODO -- remove
    VL_PRINTF("%lu %u %s\n", time, facidx, valuep);
}

void VerilatedReplay::fstCallbackVarlen(void* userDatap, uint64_t time, fstHandle facidx,
                                        const unsigned char* valuep, uint32_t len) {
    reinterpret_cast<VerilatedReplay*>(userDatap)->fstCb(time, facidx, valuep, len);
}

void VerilatedReplay::fstCallback(void* userDatap, uint64_t time, fstHandle facidx,
                                  const unsigned char* valuep) {
    // Cribbed from fstminer.c in the gtkwave repo
    uint32_t len;

    if(valuep) {
        len = strlen((const char *)valuep);
    } else {
        len = 0;
    }

    fstCallbackVarlen(userDatap, time, facidx, valuep, len);
}

void VerilatedReplay::createMod() {
    // TODO -- maybe get rid of the need for VM_PREFIX by generating these things
    m_modp = new VM_PREFIX;
    // TODO -- make VerilatedModule destructor virtual so we can delete from the base class?
#if VM_TRACE
    Verilated::traceEverOn(true);
    m_tfp = new VerilatedFstC;
    reinterpret_cast<VM_PREFIX*>(m_modp)->trace(m_tfp, 99);
    // TODO -- command line parameter
    m_tfp->open("replay.fst");
#endif  // VM_TRACE
}

void VerilatedReplay::eval() {
    // TODO -- make eval, trace and final virtual methods of VerilatedModule?
    reinterpret_cast<VM_PREFIX*>(m_modp)->eval();
}

void VerilatedReplay::trace() {
#if VM_TRACE
    if (m_tfp) m_tfp->dump(m_simTime);
#endif  // VM_TRACE
}

void VerilatedReplay::final() {
    reinterpret_cast<VM_PREFIX*>(m_modp)->final();
}
