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
/// \brief Verilator: Include for replay tool
///
///     See verilator_replay
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#ifndef _VERILATED_REPLAY_H_
#define _VERILATED_REPLAY_H_ 1  ///< Header Guard

#include "verilated.h"
#include "verilated_fst_c.h"
#include "verilated_replay_common.h"
#include "gtkwave/fstapi.h"
#include <string>
#include <map>
#include <vector>

#define QUOTE(x) #x
#define MAKE_HEADER(x) QUOTE(x.h)
#include MAKE_HEADER(VM_PREFIX)

class VerilatedReplay: private VerilatedReplayCommon {
private:
    struct FstSignal {
        size_t bits;
        vluint8_t* signal;
        vluint8_t* expected;
        FstSignal()  {}
        FstSignal(size_t _bits, vluint8_t* _signal):
            bits(_bits), signal(_signal), expected(NULL) { }
        FstSignal(size_t _bits, vluint8_t* _signal, vluint8_t* _expected):
            bits(_bits), signal(_signal), expected(_expected) { }
    };
    typedef std::map<fstHandle, FstSignal> SignalHandleMap;
    typedef std::map<std::string, FstSignal> SignalNameMap;

    struct ReplayData {
        enum ReplayType {Input, Output, Time};
        size_t size;
        ReplayType type;
        union {
            uint64_t time;
            vluint8_t* target;
        } u;
        vluint8_t* data;
    };
    typedef std::vector<ReplayData> ReplayVector;

    void createMod();
    void addSignals();
    void addInput(const std::string& fullName, vluint8_t* signal, size_t size);
    void addOutput(const std::string& fullName, vluint8_t* signal, size_t size);
    void outputCheck();
    void eval();
    void trace();
    void final();
    void addPreloadTime();
    void loadData(ReplayData::ReplayType type, fstHandle facidx,
                  const unsigned char* valuep, uint32_t len);
    void loadInput(fstHandle facidx, const unsigned char* valuep, uint32_t len);
    void loadOutput(fstHandle facidx, const unsigned char* valuep, uint32_t len);
    void replayPreloadedData();
    void loadData(uint64_t time, fstHandle facidx, const unsigned char* value,
                  uint32_t len);
    void fstCb(uint64_t time, fstHandle facidx, const unsigned char* value,
               uint32_t len);
    void handleInput(fstHandle facidx, const unsigned char* valuep, uint32_t len);
    void handleOutput(fstHandle facidx, const unsigned char* valuep, uint32_t len);
    static void fstCallback(void* userData, uint64_t time, fstHandle facidx,
                            const unsigned char* value);
    static void fstCallbackVarlen(void* userData, uint64_t time, fstHandle facidx,
                                  const unsigned char* value, uint32_t len);

    static void copyValue(unsigned char* to, const unsigned char* valuep, uint32_t len);

    std::string m_fstName;
    double& m_simTime;
    VM_PREFIX* m_modp;
    VerilatedFstC* m_tfp;
    uint64_t m_time;
    uint64_t m_preloadTime;
    bool m_preloadData;
    bool m_doTrace;
    SignalHandleMap m_inputHandles;
    SignalHandleMap m_outputHandles;
    SignalNameMap m_inputNames;
    SignalNameMap m_outputNames;
    ReplayVector m_replayData;
public:
    VerilatedReplay(const std::string& fstName, double& simTime):
        m_fstName(fstName), m_simTime(simTime), m_tfp(NULL),
        m_preloadData(false), m_doTrace(false)
    {}
    ~VerilatedReplay();
    int init();
    int replay();
    void preloadData(bool value) { m_preloadData = value; }
    void doTrace(bool value) { m_doTrace = value; }
};

#endif  // Guard
