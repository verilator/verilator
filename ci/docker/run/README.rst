Verilator Executable Docker Container
=====================================

The Verilator Executable Docker Container allows you to run Verilator
easily as a docker image, e.g.:

::

   docker run -ti verilator/verilator:latest --version

This will install the container, run the latest Verilator and print
Verilator's version.

Containers are automatically built for all released versions, so you may
easily compare results across versions, e.g.:

::

   docker run -ti verilator/verilator:4.030 --version

Verilator needs to read and write files on the local system. To simplify
this process, use the ``verilator-docker`` convenience script. This script
takes the version number, and all remaining arguments are passed through to
Verilator. e.g.:

::

   ./verilator-docker 4.030 --version

or

::

   ./verilator-docker 4.030 --cc test.v

If you prefer not to use ``verilator-docker`` you must give the container
access to your files as a volume with appropriate user rights.  For example
to Verilate test.v:

::

   docker run -ti -v ${PWD}:/work --user $(id -u):$(id -g) verilator/verilator:latest --cc test.v

This method can only access files below the current directory. An
alternative is setup the volume ``-workdir``.

You can also work in the container by setting the entrypoint (don't forget
to mount a volume if you want your work persistent):

::

   docker run -ti --entrypoint /bin/bash verilator/verilator:latest

You can also use the container to build Verilator at a specific commit:

::

   docker build --build-arg SOURCE_COMMIT=<commit> .


Internals
---------

The Dockerfile builds Verilator and removes the tree when completed to
reduce the image size. The entrypoint is set as a wrapper script
(``verilator-wrap.sh``). That script 1. calls Verilator, and 2. copies the
Verilated runtime files to the ``obj_dir`` or the ``-Mdir``
respectively. This allows the user to have the files to they may later
build the C++ output with the matching runtime files. The wrapper also
patches the Verilated Makefile accordingly.

There is also a hook defined that is run by docker hub via automated
builds.
