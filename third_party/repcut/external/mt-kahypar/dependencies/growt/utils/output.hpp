#pragma once

/*******************************************************************************
 * output.hpp
 *
 * This file contains an output type, that can be used to either represent a
 * file stream, or the normal output stream (cout)
 * - this is really useful if different outputs should be channeled to different
 *   files/output streams
 * - there are also some convenience/pretty paint options like:
 *   - colors
 *   - width objects, that can be passed through a stream
 *   - the possibility to print the binary+hex representation of numbers
 *
 *
 * Part of my utils library utils_tm - https://github.com/TooBiased/utils_tm.git
 *
 * Copyright (C) 2019 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#include <fstream>
#include <iostream>
#include <sstream>

namespace utils_tm
{
namespace out_tm
{


using manipulator_type = std::ostream& (*)(std::ostream&);

// DEFINES THE OUTPUT TYPE THE *************************************************
// DEVICE CAN BE CHANGED FROM TERMINAL TO FILE AND BACK ************************
class output_type
{
  public:
    output_type() : _is_fstream(0) { _outstream = &(std::cout); }

    void set_terminal()
    {
        cleanup();
        _is_fstream = false;
        _outstream  = &(std::cout);
    }

    void set_file(const std::string& name)
    {
        cleanup();

        std::ofstream* fout =
            new std::ofstream(name, std::ofstream::out | std::ofstream::app);
        if (!fout->is_open())
        {
            std::cerr << "fstream is not open" << std::endl;
            set_terminal();
            return;
        }

        _is_fstream = true;
        _outstream  = fout;
    }

    void disable() { cleanup(); }


    template <class T>
    friend output_type& operator<<(output_type& out, T&& t);
    friend output_type& operator<<(output_type& out, manipulator_type t);

  private:
    std::ostream* _outstream;
    bool          _is_fstream;

    void cleanup()
    {
        if (_is_fstream)
        {
            std::ofstream* fout = static_cast<std::ofstream*>(_outstream);
            if (fout->is_open()) fout->close();
            delete fout;
        }
        _is_fstream = false;
        _outstream  = nullptr;
    }
};



// base case, everything is output through the device
template <typename T>
inline output_type& operator<<(output_type& cons, T&& t)
{
    if (!cons._outstream) return cons;
    *(cons._outstream) << std::forward<T>(t);
    return cons;
}

// necessary for endl and flush
// using omanip_t = std::ostream& (*) (std::ostream &);
inline output_type& operator<<(output_type& cons, manipulator_type t)
{
    if (!cons._outstream) return cons;
    *(cons._outstream) << t;
    return cons;
}


// THE STATIC OUTPUT OBJECT (THIS REPLACES std::cout) **************************
inline output_type& out()
{
    static output_type static_out;
    return static_out;
}




template <class Out>
class locally_buffered_output
{
  private:
    using stream_type = Out;

    stream_type&      _out;
    std::stringstream _buffer;

  public:
    locally_buffered_output(stream_type& out) : _out(out) {}
    locally_buffered_output(const locally_buffered_output&)            = delete;
    locally_buffered_output& operator=(const locally_buffered_output&) = delete;
    locally_buffered_output(locally_buffered_output&&)            = default;
    locally_buffered_output& operator=(locally_buffered_output&&) = default;
    ~locally_buffered_output() { _out << _buffer.str() << std::flush; }

    template <class O, class T>
    friend locally_buffered_output<O>&
    operator<<(locally_buffered_output<O>& out, T&& t);
    template <class O>
    friend locally_buffered_output<O>&
    operator<<(locally_buffered_output<O>& out, manipulator_type t);
};

// base case, everything is output through the device
template <class O, class T>
inline locally_buffered_output<O>&
operator<<(locally_buffered_output<O>& lbo, T&& t)
{
    lbo._buffer << std::forward<T>(t);
    return lbo;
}

// necessary for endl and flush
// using omanip_t = std::ostream& (*) (std::ostream &);
template <class O>
inline locally_buffered_output<O>&
operator<<(locally_buffered_output<O>& lbo, manipulator_type t)
{
    lbo._buffer << t;
    lbo._out << lbo._buffer.str() << std::flush;
    lbo._buffer.str("");
    return lbo;
}


inline locally_buffered_output<output_type>& buffered_out()
{
    static thread_local locally_buffered_output<output_type> local_out(out());
    return local_out;
}




// CHANGING COLORS OF OUTPUTS **************************************************
enum class color
{
    reset    = 0,
    black    = 30,
    red      = 31,
    green    = 32,
    yellow   = 33,
    blue     = 34,
    magenta  = 35,
    cyan     = 36,
    white    = 37,
    bblack   = 40,
    bred     = 41,
    bgreen   = 42,
    byellow  = 43,
    bblue    = 44,
    bmagenta = 45,
    bcyan    = 46,
    bwhite   = 47
};

inline std::ostream& operator<<(std::ostream& o, color c)
{
    int ccode = static_cast<int>(c);
    if (ccode >= 40)
        o << "\033[1;" << ccode - 10 << "m";
    else
        o << "\033[0;" << ccode << "m";
    return o;
}

// CONTROLS THE WIDTH OF THE OUTPUT ********************************************
class width_type
{
  public:
    explicit width_type(size_t width = 0) : _width(width) {}

    size_t get_width() { return _width; }

  private:
    size_t _width;
};

inline width_type width(size_t w) { return width_type(w); }

inline std::ostream& operator<<(std::ostream& o, width_type w)
{
    o.width(w.get_width());
    return o;
}


// PREPARATION FOR OUTPUT MANIPULATORS *****************************************
struct empty_output_type
{
};

// forward declaration
template <class T>
class manipulated_output_type;

// important specialisation
template <>
class manipulated_output_type<empty_output_type>
{
  public:
    manipulated_output_type(width_type width)
        : _width(width), _color(color::reset)
    {
    }
    manipulated_output_type(color col) : _width(0), _color(col) {}

    manipulated_output_type(manipulated_output_type m0,
                            manipulated_output_type m1)
        : _width((m0._width.get_width() > 0) ? m0._width : m1._width),
          _color((m0._color != color::reset) ? m0._color : m1._color)
    {
        // it would be cool, to do some sanity checks here, i.e., not both
        // widths are set, and not both colors are set
    }

  private:
    width_type _width;
    color      _color;

    template <class U>
    friend std::ostream&
    operator<<(std::ostream& o, manipulated_output_type<U> w);

    template <class U>
    friend class manipulated_output_type;
};


// main implementation
template <class T>
class manipulated_output_type
{
  public:
    manipulated_output_type(T                                          content,
                            manipulated_output_type<empty_output_type> m)
        : _width(m._width), _color(m._color), _content(content)
    {
    }

    manipulated_output_type(manipulated_output_type                    m,
                            manipulated_output_type<empty_output_type> o)
        : _width((m._width.get_width() != 0) ? m._width : o._width),
          _color((m._color != color::reset) ? m._color : o._color),
          _content(m._content)
    {
        // it would be cool, to do some sanity checks here, i.e., not both
        // widths are set, and not both colors are set
    }

    // template <class U>
    // manipulated_output_type(manipulated_output_type    m,
    //                         manipulated_output_type<U> o)
    // {
    //     // it would be cool to have some better error outputs i.e., this
    //     // function does not exist, because it indicates, that two
    //     // manipulated_output_types with content are combined
    // }

  private:
    width_type _width;
    color      _color;
    T          _content;

    template <class U>
    friend std::ostream&
    operator<<(std::ostream& o, manipulated_output_type<U> w);
    template <class U>
    friend class manipulated_output_type;
};


// output operators for manipulated output types
template <class T>
inline std::ostream& operator<<(std::ostream& o, manipulated_output_type<T> m)
{
    if (m._color != color::reset) o << m._color;
    if (m._width.get_width() > 0) o << m._width;
    o << m._content;
    if (m._color != color::reset) o << color::reset;
    if (m._width.get_width() > 0) o << " ";
    return o;
}

template <>
inline std::ostream&
operator<<(std::ostream& o, manipulated_output_type<empty_output_type> m)
{
    if (m._color != color::reset) o << m._color;
    if (m._width.get_width() > 0) o << m._width;
    return o;
}


// adding together two content free manipulated_output_types
inline manipulated_output_type<empty_output_type>
operator+(manipulated_output_type<empty_output_type> m0,
          manipulated_output_type<empty_output_type> m1)
{
    return manipulated_output_type<empty_output_type>(m0, m1);
}

// adding content to a previously content free manipulated_output_type
template <
    class T,
    std::enable_if_t<
        !std::is_convertible_v<T, manipulated_output_type<empty_output_type>>,
        int> = 0>
inline manipulated_output_type<T>
operator+(T t, manipulated_output_type<empty_output_type> m)
{
    return manipulated_output_type<T>(t, m);
}

template <
    class T,
    std::enable_if_t<
        !std::is_convertible_v<T, manipulated_output_type<empty_output_type>>,
        int> = 0>
inline manipulated_output_type<T>
operator+(manipulated_output_type<empty_output_type> m, T t)
{
    return manipulated_output_type<T>(t, m);
}

// adding content to a color somehow this did not work before
template <
    class T,
    std::enable_if_t<
        !std::is_convertible_v<T, manipulated_output_type<empty_output_type>>,
        int> = 0>
inline manipulated_output_type<T> operator+(T t, color c)
{
    return manipulated_output_type<T>(t, c);
}

template <
    class T,
    std::enable_if_t<
        !std::is_convertible_v<T, manipulated_output_type<empty_output_type>>,
        int> = 0>
inline manipulated_output_type<T> operator+(color c, T t)
{
    return manipulated_output_type<T>(t, c);
}

// adding two manipulated_content_types, one with one without context
template <class T>
inline manipulated_output_type<T>
operator+(manipulated_output_type<T>                 mt,
          manipulated_output_type<empty_output_type> me)
{
    return manipulated_output_type<T>(mt, me);
}

template <class T>
inline manipulated_output_type<T>
operator+(manipulated_output_type<empty_output_type> me,
          manipulated_output_type<T>                 mt)
{
    return manipulated_output_type<T>(mt, me);
}


// Some Helper Functions *******************************************************
template <class T>
inline manipulated_output_type<T> width(size_t w, T t)
{
    return width_type(w) + t;
}

template <class T>
manipulated_output_type<T>
expected(T value, T expectation, color wcolor = color::red)
{
    return value + manipulated_output_type<empty_output_type>(
                       (value == expectation) ? color::reset : wcolor);
}

// PRINT BITS STUFF ************************************************************
template <class int_type>
std::string bit_print(int_type t)
{
    constexpr size_t length = sizeof(int_type) * 8;

    std::ostringstream buffer;
    size_t             temp = 1ull << (length - 1);

    size_t i = 0;
    while (temp > 0)
    {
        buffer << ((temp & t) ? 1 : 0);
        if (i++ >= 7)
        {
            i = 0;
            buffer << " ";
        }
        temp >>= 1;
    }

    return buffer.str();
}

template <class int_type>
std::string hex_print(int_type t)
{
    constexpr size_t length  = sizeof(int_type) * 8;
    constexpr char   table[] = {'0', '1', '2', '3', '4', '5', '6', '7',
                                '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};

    std::ostringstream buffer;
    int                shift = length - 4;

    while (shift > 0)
    {
        buffer << table[(t >> shift) & 15] << table[(t >> (shift - 4)) & 15]
               << " ";
        shift -= 8;
    }

    return buffer.str();
}


} // namespace out_tm
} // namespace utils_tm
