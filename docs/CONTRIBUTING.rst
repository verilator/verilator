.. SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Contributing to Verilator
=========================

Thanks for using Verilator! We welcome your contributions in whatever form.

This contributing document contains some suggestions that may make
contributions flow more efficiently.


Did you find a Verilator bug?
-----------------------------

- Please **ensure the bug was not already reported** by searching
  `Verilator Issues <https://verilator.org/issues>`__.

- Please **download the latest development GitHub version**, build, and see
  if the issue has been fixed.

- If you're unable to find an open issue addressing the problem, `open a
  new Verilator issue <https://verilator.org/issues/new>`__.

  - Be sure to include a **code sample** or an **executable test case**
    demonstrating the bug and expected behavior that is not occurring.

  - The ideal example works against other simulators, and is in the
    test_regress/t test format, as described in `Verilator Internals
    Documentation
    <https://github.com/verilator/verilator/blob/master/docs/internals.rst>`__.


Did you write a patch that fixes a Verilator bug?
-------------------------------------------------

- Please `Open a new Verilator issue <https://verilator.org/issues/new>`__
  if there is not one already describing the bug.

- Please `Open a Verilator pull request
  <https://github.com/verilator/verilator/pulls>`__.

- See the coding conventions, and other developer information in
  ``docs/internals.rst`` in the distribution, or as rendered at `Verilator
  Internals Documentation
  <https://github.com/verilator/verilator/blob/master/docs/internals.rst>`__.

- Verilator uses GitHub Actions to provide continuous integration. You may
  want to enable Actions on your GitHub branch to ensure your changes keep
  the tests passing.

- Your source-code contributions must be certified as open source, under
  the `Developer Certificate of Origin
  <https://developercertificate.org/>`__. On your first contribution, you
  must either:

  - Have your patch include the addition of your name to `docs/CONTRIBUTORS
    <CONTRIBUTORS>`__ (preferred).

  - Email, or post in an issue a statement that you certify your
    contributions.

  - In any of these cases, your name will be added to `docs/CONTRIBUTORS
    <CONTRIBUTORS>`__ and you are agreeing all future contributions are
    also certified.

  - We occasionally accept contributions where people do not want their
    name published. Please email us; you must still privately certify your
    contribution.

- Your test contributions are generally considered released into the
  Creative Commons Public Domain (CC0), unless you request otherwise, or
  put a GNU/Artistic license on your file.

- Most important is we get your patch.


Do you have questions on Verilator?
-----------------------------------

- Please see FAQ section and rest of the `Verilator manual
  <https://verilator.org/verilator_doc.html>`__, or `Verilator manual (PDF)
  <https://verilator.org/verilator_doc.pdf>`__.

- Ask any question in the `Verilator forum
  <https://verilator.org/forum>`__.


AI Policy
---------

Verilator follows the Linux Foundation recommendations regarding the usage
of Generative Large Language Model Artificial Intelligence (LLM-AI) tools
and agents for all contributions to the project, including source code,
test benches, and documentation.

AI assistants and automated agents are not permitted to sign off on
contributions. A human submitter is strictly responsible for reviewing,
verifying, and testing all AI-generated content. By submitting, the
contributor certifies that the generated content is effectively their work
product and adheres to project standards. This accountability is affirmed
when the human contributor signs the Developer Certificate of Origin (DCO)
as outlined in ``docs/CONTRIBUTORS``.

Contributors are encouraged to disclose the significant use of generative
AI tools in their commit messages or Pull Request descriptions to maintain
transparency.

Contributors must ensure that the terms and conditions of the generative AI
tool do not place any contractual restrictions on the tool's output that
are inconsistent with Verilator's open-source licenses, the project's
intellectual property policies, or the Open Source Definition.

If any pre-existing copyrighted materials (including third-party
open-source code or documentation) are included in the AI tool's output,
the contributor must confirm prior to submission that they have explicit
permission from the third-party owners to use, modify, and distribute those
materials under terms compliant with Verilator's licensing policies.


Code of Conduct
---------------

Our contributors and participants pledge to make participation in our
project and our community a positive experience for everyone. We follow the
`Contributor Covenant version 1.4
<https://www.contributor-covenant.org/version/1/4/code-of-conduct/>`__.

Thanks!
