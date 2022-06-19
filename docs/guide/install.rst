.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Installation:

************
Installation
************

This section discusses how to install Verilator.

.. _Package Manager Quick Install:

Package Manager Quick Install
=============================

Using a distribution's package manager is the easiest way to get
started. (Note packages are unlikely to have the most recent version, so
:ref:`Git Install`, might be a better alternative.) To install as a
package:

::

   apt-get install verilator   # On Ubuntu

For other distributions refer to `Repology Verilator Distro Packages
<https://repology.org/project/verilator>`__.

.. _Git Install:

Git Quick Install
=================

Installing Verilator from Git provides the most flexibility. For additional
options and details see :ref:`Detailed Build Instructions` below.

In brief, to install from git:

::

   # Prerequisites:
   #sudo apt-get install git perl python3 make autoconf g++ flex bison ccache
   #sudo apt-get install libgoogle-perftools-dev numactl perl-doc
   #sudo apt-get install libfl2  # Ubuntu only (ignore if gives error)
   #sudo apt-get install libfl-dev  # Ubuntu only (ignore if gives error)
   #sudo apt-get install zlibc zlib1g zlib1g-dev  # Ubuntu only (ignore if gives error)

   git clone https://github.com/verilator/verilator   # Only first time

   # Every time you need to build:
   unsetenv VERILATOR_ROOT  # For csh; ignore error if on bash
   unset VERILATOR_ROOT  # For bash
   cd verilator
   git pull         # Make sure git repository is up-to-date
   git tag          # See what versions exist
   #git checkout master      # Use development branch (e.g. recent bug fixes)
   #git checkout stable      # Use most recent stable release
   #git checkout v{version}  # Switch to specified release version

   autoconf         # Create ./configure script
   ./configure      # Configure and create Makefile
   make -j `nproc`  # Build Verilator itself (if error, try just 'make')
   sudo make install


.. _Detailed Build Instructions:

Detailed Build Instructions
===========================

This section describes details of the build process, and assumes you are
building from Git. For using a pre-built binary for your Linux
distribution, see instead :ref:`Package Manager Quick Install`.


OS Requirements
---------------

Verilator is developed and has primary testing on Ubuntu, with additional
testing on FreeBSD and Apple OS-X. Versions have also built on Red Hat
Linux, and other flavors of GNU/Linux-ish platforms. Verilator also works
on Windows Subsystem for Linux (WSL2), Windows under Cygwin, and Windows
under MinGW (gcc -mno-cygwin). Verilated output (not Verilator itself)
compiles under all the options above, plus using MSVC++.


Install Prerequisites
---------------------

To build or run Verilator, you need these standard packages:

::

   sudo apt-get install git perl python3 make
   sudo apt-get install g++  # Alternatively, clang
   sudo apt-get install libgz  # Non-Ubuntu (ignore if gives error)
   sudo apt-get install libfl2  # Ubuntu only (ignore if gives error)
   sudo apt-get install libfl-dev  # Ubuntu only (ignore if gives error)
   sudo apt-get install zlibc zlib1g zlib1g-dev  # Ubuntu only (ignore if gives error)

To build or run Verilator, the following are optional but should be installed
for good performance:

::

   sudo apt-get install ccache  # If present at build, needed for run
   sudo apt-get install libgoogle-perftools-dev numactl

The following is optional but is recommended for nicely rendered command line
help when running Verilator:

::

   sudo apt-get install perl-doc

To build Verilator you will need to install these packages; these do not
need to be present to run Verilator:

::

   sudo apt-get install git autoconf flex bison

Those developing Verilator itself may also want these (see internals.rst):

::

   sudo apt-get install gdb graphviz cmake clang clang-format-11 gprof lcov
   sudo apt-get install yapf3
   sudo pip3 install sphinx sphinx_rtd_theme sphinxcontrib-spelling breathe
   cpan install Pod::Perldoc
   cpan install Parallel::Forker


Install SystemC
^^^^^^^^^^^^^^^

If you will be using SystemC (vs straight C++ output), download `SystemC
<https://www.accellera.org/downloads/standards/systemc>`__.  Follow their
installation instructions. You will need to set the
:option:`SYSTEMC_INCLUDE` environment variable to point to the include
directory with ``systemc.h`` in it, and set the :option:`SYSTEMC_LIBDIR`
environment variable to point to the directory with ``libsystemc.a`` in it.


Install GTKWave
^^^^^^^^^^^^^^^

To make use of Verilator FST tracing you will want `GTKwave
<http://gtkwave.sourceforge.net/>`__ installed, however this is not
required at Verilator build time.


Obtain Sources
--------------

Get the sources from the git repository: (You need do this only once,
ever.)

::

   git clone https://github.com/verilator/verilator   # Only first time
   ## Note the URL above is not a page you can see with a browser, it's for git only

Enter the checkout and determine what version/branch to use:

::

   cd verilator
   git pull        # Make sure we're up-to-date
   git tag         # See what versions exist
   #git checkout master      # Use development branch (e.g. recent bug fix)
   #git checkout stable      # Use most recent release
   #git checkout v{version}  # Switch to specified release version


Auto Configure
--------------

Create the configuration script:

::

   autoconf        # Create ./configure script


Eventual Installation Options
-----------------------------

Before configuring the build, you have to decide how you're going to
eventually install Verilator onto your system. Verilator will be compiling
the current value of the environment variables :option:`VERILATOR_ROOT`,
:option:`SYSTEMC_INCLUDE`, and :option:`SYSTEMC_LIBDIR` as defaults into
the executable, so they must be correct before configuring.

These are the installation options:


1. Run-in-Place from VERILATOR_ROOT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Our personal favorite is to always run Verilator in-place from its Git
directory. This allows the easiest experimentation and upgrading, and
allows many versions of Verilator to co-exist on a system.

::

   export VERILATOR_ROOT=`pwd`   # if your shell is bash
   setenv VERILATOR_ROOT `pwd`   # if your shell is csh
   ./configure
   # Running will use files from $VERILATOR_ROOT, so no install needed

Note after installing (below steps), a calling program or shell must set
the environment variable :option:`VERILATOR_ROOT` to point to this Git
directory, then execute ``$VERILATOR_ROOT/bin/verilator``, which will find
the path to all needed files.


2. Install into a specific location
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You may eventually be installing onto a project/company-wide "CAD" tools
disk that may support multiple versions of every tool. Tell configure the
eventual destination directory name.  We recommend the destination location
include the Verilator version name:

::

   unset VERILATOR_ROOT      # if your shell is bash
   unsetenv VERILATOR_ROOT   # if your shell is csh
   # For the tarball, use the version number instead of git describe
   ./configure --prefix /CAD_DISK/verilator/`git describe | sed "s/verilator_//"`

Note after installing (below steps), if you use `modulecmd
<http://modules.sourceforge.net/>`__, you'll want a module file like the
following:

::

   set install_root /CAD_DISK/verilator/{version-number-used-above}
   unsetenv VERILATOR_ROOT
   prepend-path PATH $install_root/bin
   prepend-path MANPATH $install_root/man
   prepend-path PKG_CONFIG_PATH $install_root/share/pkgconfig


3. Install into a Specific Path
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You may eventually install Verilator into a specific installation prefix,
as most GNU tools support:

::

   unset VERILATOR_ROOT      # if your shell is bash
   unsetenv VERILATOR_ROOT   # if your shell is csh
   ./configure --prefix /opt/verilator-VERSION

Then after installing (below steps) you will need to add
``/opt/verilator-VERSION/bin`` to your ``$PATH`` environment variable.


4. Install System Globally
^^^^^^^^^^^^^^^^^^^^^^^^^^

The final option is to eventually install Verilator globally, using
configure's default system paths:

::

   unset VERILATOR_ROOT      # if your shell is bash
   unsetenv VERILATOR_ROOT   # if your shell is csh
   ./configure

Then after installing (below) the binaries should be in a location that is
already in your ``$PATH`` environment variable.


Configure
---------

The command to configure the package was described in the previous step.
Developers should configure to have more complete developer tests.
Additional packages may be required for these tests.

::

   export VERILATOR_AUTHOR_SITE=1    # Put in your .bashrc
   ./configure --enable-longtests  ...above options...


Compile
-------

Compile Verilator:

::

   make -j `nproc`  # Or if error on `nproc`, the number of CPUs in system


Test
----

Check the compilation by running self-tests:

::

   make test


Install
-------

If you used any install option other than the `1. Run-in-Place from
VERILATOR_ROOT <#_1_run_in_place_from_verilator_root>`__ scheme, install
the files:

::

   make install


.. Docker Build Environment

.. include:: ../../ci/docker/buildenv/README.rst


.. Docker Run Environment

.. include:: ../../ci/docker/run/README.rst
