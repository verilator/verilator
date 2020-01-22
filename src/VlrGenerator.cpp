#include "VlrGenerator.h"
#include "V3Error.h"
#include "gtkwave/fstapi.h"

void VlrGenerator::searchFst() {
    openFst(string(m_opts.fst()));
    VerilatedReplayCommon::searchFst(m_opts.scope());
}

string VlrGenerator::replayName(const string& fullName) {
        string sigName(fullName);

        // TODO -- add a trailing dot for the user if they don't
        if (m_opts.replayTop()) {
            string replayTop(m_opts.replayTop());
            size_t pos = sigName.find(replayTop);
            if (pos != 0) {
                cout << sigName << " did not start with " << replayTop << endl;
                exit(-1);
            }

            sigName = sigName.substr(replayTop.length());
        }

        return sigName;
}

void VlrGenerator::emitVltCode() {
    // TODO -- use V3OutCFile
    cout << "#include \"verilated_replay.h\"" << endl;
    cout << endl;
    cout << "void VerilatedReplay::addSignals() {" << endl;

    for (VarMap::iterator it = m_inputs.begin(); it != m_inputs.end(); ++it) {
        string sigName = replayName(it->second.fullName);

        cout << "    addInput(\"" << it->second.fullName <<
             "\", &(m_modp->" << sigName <<
             "), " << it->second.hier.u.var.length << ");" << endl;
        // TODO -- sizof check (FST vs VLT)
    }

    if (m_opts.checkOutputs()) {
        for (VarMap::iterator it = m_outputs.begin(); it != m_outputs.end(); ++it) {
            string sigName = replayName(it->second.fullName);

            cout << "    addOutput(\"" << it->second.fullName <<
                 "\", &(m_modp->" << sigName <<
                 "), " << it->second.hier.u.var.length << ");" << endl;
            // TODO -- sizof check (FST vs VLT)
        }
    }

    cout << "}" << endl;
}
