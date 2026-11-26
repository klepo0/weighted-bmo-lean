# Paper: Maximal inequalities and weighted BMO processes

Local copy of the arXiv version the Lean formalization in this repository follows.

| | |
|---|---|
| Title | Maximal inequalities and weighted BMO processes |
| Author | Khoa Lê |
| arXiv | [2211.15550v3](https://arxiv.org/abs/2211.15550v3) (math.PR) |
| Version | v3, submitted 19 Dec 2022 |
| License | arXiv non-exclusive distribution licence (as set by the author for this submission) |

## Files

- `2211.15550v3.pdf` — the published PDF as served by arXiv (13 pages).
- `source.tar.gz` — the unmodified arXiv e-print tarball (`https://arxiv.org/e-print/2211.15550v3`).
- `src/weightedBMO.tex` — LaTeX source, plus `src/weightedBMO.bbl` and the
  bundled `src/orcidlink.sty`.

```text
4b4d438fe201df6e000303c98bb529016a75bfbdf46da60a9cd72d6d364d1ac0  2211.15550v3.pdf
ddf41ca2a3f36b4e9933c47354d7fe8d8fd8fe202d9ab1e98bc370b1a81e1271  source.tar.gz
11fd86ac3cb6969eddf6fcf425a0794c30903ea60e008a876b499593d2bb5db8  src/weightedBMO.tex
898f518c3d4851b63ee12fa5c1ec9142b3971e2f2042f2d491ca4491a65aaeeb  src/weightedBMO.bbl
2941c36b772ae89cbcaca60fb14d888b59e41733c6255c5a0ef23043c190bc74  src/orcidlink.sty
```

## Recompiling

`latexmk -pdf weightedBMO.tex` in `src/` needs `bbm.sty`, `libertine`, `newtxmath`
and `microtype`; `bbm.sty` is not part of the TeX Live installation in this VM
(`kpsewhich bbm.sty` fails), so the checked-in PDF is the arXiv build rather than
a local one.
