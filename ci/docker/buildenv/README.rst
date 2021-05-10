Verilator Build Docker Container
================================

This Verilator Build Docker Container is set up to compile and test a
Verilator build. It uses the following parameters:

-  Source repository (default: https://github.com/verilator/verilator)

-  Source revision (default: master)

-  Compiler (GCC 9.3.0, clang 10.0.0, default: 9.3.0)

The container is published as ``verilator/verilator-buildenv`` on `docker
hub
<https://hub.docker.com/repository/docker/verilator/verilator-buildenv>`__.

To run the basic build using the current Verilator master:

::

   docker run -ti verilator/verilator-buildenv

To also run tests:

::

   docker run -ti verilator/verilator-buildenv test

To change the compiler:

::

   docker run -ti -e CC=clang-10 -e CXX=clang++-10 verilator/verilator-buildenv test

The tests that involve gdb are not working due to security restrictions.
To run those too:

::

   docker run -ti -e CC=clang-10 -e CXX=clang++-10 --cap-add=SYS_PTRACE --security-opt seccomp=unconfined verilator/verilator-buildenv test

Rather then building using a remote git repository you may prefer to use a
working copy on the local filesystem. Mount the local working copy path as
a volume and use that in place of git. When doing this be careful to have
all changes committed to the local git area. To build the current HEAD from
top of a repository:

::

   docker run -ti -v ${PWD}:/tmp/repo -e REPO=/tmp/repo -e REV=`git rev-parse --short HEAD` --cap-add=SYS_PTRACE --security-opt seccomp=unconfined verilator/verilator-buildenv test


Rebuilding
----------

To rebuild the Verilator-buildenv docker image, run:

::

   docker build .

This will also build SystemC under all supported compiler variants to
reduce the SystemC testing time.
