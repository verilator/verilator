#pragma once

#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>

// adapted from KaHyPar
class HFCLogger {
public:
    explicit HFCLogger(const bool newline) : _newline(newline), _oss() {}
    template<typename T>
    HFCLogger& operator<<(const T& output) {
        _oss << output << ' ';
        return *this;
    }

    HFCLogger& operator<<(decltype(std::left)& output) {
        _oss << output;
        return *this;
    }

    HFCLogger& operator<<(const decltype(std::setw(1))& output) {
        _oss << output;
        return *this;
    }

    ~HFCLogger() {
        std::cout << _oss.str();
        if (_newline) {
            std::cout << std::endl;
        } else {
            std::cout << ' ';
        }
    }

private:
    bool _newline;
    std::ostringstream _oss;
};

class HFCLoggerVoidify {
public:
    void operator&(HFCLogger&) {}
};

#define V(X) #X << "=" << X

#define LOGGER_CC(cond, newline) !(cond) ? (void) 0 : HFCLoggerVoidify() & HFCLogger(newline)

#define LOGGER LOGGER_CC(log, true)
#define LOGGER_WN LOGGER_CC(log, false)
