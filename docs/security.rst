.. for github, vim: syntax=reStructuredText

Security Policy
===============

If you believe you have found a security issue in any Verilator-owned
repository, create a `GitHub repository security advisory
<https://docs.github.com/en/code-security/security-advisories/working-with-repository-security-advisories/creating-a-repository-security-advisory>`__.
We request that you please not publicly disclose the issue until it has
been addressed by us.

SystemVerilog Security
----------------------

The SystemVerilog language includes `$system`, etc. operating system calls,
and as such executables created by Verilator should be considered insecure.
In contrast, it is a security issue if a Verilator-created data file, such
as a coverage data file, when read with `verilator_coverage`, allows
arbitrary code execution.

Bug bounties
------------

While we encourage reports of suspected security problems, we are an open
source project, and do not run any bug bounty programs.

Preferred Languages
-------------------

We prefer all communications to be in English.

Policy
------

We follow the principle of `Coordinated Vulnerability Disclosure
<https://en.wikipedia.org/wiki/Coordinated_vulnerability_disclosure>`__.

Distribution
------------

SPDX-License-Identifier: CC0-1.0
