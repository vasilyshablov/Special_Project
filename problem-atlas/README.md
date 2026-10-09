# The Atlas of Hard Problems

`atlas.pdf`: 100 open problems in mathematics, ranked by tier (beyond Fields, Fields-level, major
breakthrough, strong research). Each problem has a difficulty score and a "raw-reasoning fit" score, and the
atlas closes with an honest assessment of which ones discrete mathematics plus Lean could plausibly reach.

All tiers, scores and odds are Claude's subjective judgements, as of 2026.

- `build.py`: the problem data, plus generation of the table, heat map and chart data (`gen_*`).
- `table_frame.tex`: the longtable header; `build.py` fills in the rows.
- `atlas.tex`: the document.

Rebuild with `python3 build.py && pdflatex atlas.tex && pdflatex atlas.tex`.

## Update, 9 October 2026

The atlas now records AI claims from `github.com/openai/math` (released 6 October 2026, 372 result families) and
from earlier 2026 announcements (the Navier–Stokes and 3D Euler blow-up claims). These live in `CLAIMS` in
`build.py`.

- **Coverage:** 30 of the 100 problems carry a claim: 12 claimed resolutions and 18 claimed partial results.
- **Verification:** none of the claims is peer reviewed.
- **Picks:** Seymour's conjecture was replaced in the picks by "audit an AI claim".
