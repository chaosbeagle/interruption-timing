# Interruption Timing under Hidden Information

[繁體中文](../README.md) · [English](../README.en.md) · [日本語](../README.ja.md)

- [Paper](manuscript.pdf)
- [LaTeX source](manuscript.tex), using the AMS `amsart` class
- [TikZ figures](figures/)
- [Formal proofs and theorem correspondence](../proofs/README.md)

Compile from this directory with XeLaTeX:

```sh
xelatex manuscript.tex
xelatex manuscript.tex
```

The bibliography is included in the source. Japanese card-name footnotes link
to the official card entries. Install Noto Serif CJK JP, Yu Gothic, or MS Gothic
for the Japanese text; the source selects the first available font in that order.

To compile a figure separately, run XeLaTeX on its `*_standalone.tex` file
from the `figures` directory.
