# Project log and handoff

This file is the single entry point to everything in this repository. All work is on
branch `claude/lean-math-problems-vt9qbw`; nothing has been merged to `main`.

## Environment (for a fresh session)

- **Lean toolchain:** v4.33.1 with Mathlib. The Lean project used for checking is
  `/home/user/work/formal-conjectures`. Before using `lake`, run
  `export PATH=$HOME/.elan/bin:$PATH`.
- **Check a file:** `cd /home/user/work/formal-conjectures && lake env lean <path/to/File.lean>`.
- **First Mathlib import is slow.** Reading the ~5 GB of Mathlib build files from a cold
  disk takes about 8 minutes. Warm the page cache first:
  `find .lake -name "*.olean*" | xargs -P 8 -n 200 cat > /dev/null` (about 3 minutes).
- **LaTeX:** `pdflatex` works and `pgfplots` is available. Use `\usepackage[T1]{fontenc}` and
  `\usepackage{lmodern}` to avoid bitmap fonts.
- **Python:** `scipy` was pip-installed during the session; `matplotlib` is not installed.

## 1. Open-problem proofs (earlier sessions)

| Folder | What | Status |
|---|---|---|
| `lean-graffiti-100/` | Lean proof plus paper for WOWII (Graffiti) Conjecture 100 | Done. Prior resolution found and credited. |
| `lean-unique-multiset-sums/` | Lean proof of the 2^(n-1) unique-multiset-sum bound | Done. Prior work found and credited. |
| `oeis-A397683/` | Lean proof plus 4-page paper for the OEIS A397683 conjecture, via Cohen's consecutive-primitive-roots theorem (taken as an explicit hypothesis) | Done. Apparently first. |

## 2. `formal-trust-thesis/`: mathematics without human understanders

Context: a debate with a friend (Тала), who argued that AI can't handle open "why" questions
and that human mathematicians are still needed.

- **`TrustThesis.lean`** (no `sorry`). Proves two kinds of statement:
  - *Producer-independence:* whether a proof is valid never depends on who produced it.
  - *Trust transfer:* a Bayesian track record pushes trust in a prover toward 1 but never
    reaches it, plus the condition under which it outweighs a community, and why
    verification is blind to tasks that can't be checked.

  It also models "what is a human?" through sorites and replacement dilemmas.
- **`paper/paper.pdf`:** 6-page draft, "Mathematics Without Human Understanders".

## 3. `fruitfulness/`: what is the fruitfulness of a mathematical idea? (main project, this session)

Start with `fruitfulness/README.md`. The key documents:

| File | Content |
|---|---|
| `paper/paper.pdf` | Paper v2 (14 pages): *Fruitfulness as Compression: An Exact Calculus of Naming, a Speed Limit, and a Measurement of All of Mathlib* |
| `notes/thoughts.pdf` | First working notes: connections to proof complexity, logical depth, compression progress, the glue law, Simon, Wigner |
| `notes/where_we_are.pdf` | Plain explainer of the Lucas conjecture and of Frege vs Extended Frege, with an honest status table |
| `notes/attempt.pdf` | Attack on the Lucas conjecture: binary case proved by hand, the obstruction, attack routes, and Frege vs EF difficulty |

### Lean files (all compile, no `sorry`, standard axioms only)

- **`Fruitfulness.lean`: single names and unfolding.**
  - Naming a body of size `b` used `k` times saves exactly `(k-1)(b-1)-1`.
  - Unfolding at most doubles per result (`unfold ≤ S·2^i`), and this is attained.
  - Sharp d-bonacci bound for bounded citations (`unfold_le_tb`, attained by `windowLib`).
  - Fibonacci library: `F(i+3)-1`.
- **`Naming.lean`: the calculus of naming.**
  - Exact value of naming `v` in any library: `(occ-1)(W-1)-1` (`gain_eq`).
  - Rank-one, Schur-complement-style updates (`W_insert`, `P_insert`, `occ_insert`).
  - Every used result occurs (`one_le_occ`).
  - **Concepts are substitutes:** the savings function is submodular (`substitutes`).
  - **Bounded readers see complements** (`comprehension_complements`).
- **`SpeedLimit.lean`: the speed limit of compression.**
  - Every unfolded size is at most `28·(5/4)^C` (`u_le`), via the potential
    `4S1+2S2+S3+28` on top-j sums. The weights came from LP; the cases are checked by
    `omega` (`key_small`).
  - Fibonacci library at cost `3(n+1)` reaches `F(n+3)-1`, and each step is readable with
    3 symbols.
  - Lucas library reaches exactly `2L_m-2` at cost `3m` (`lucasLib_top`, `lucasLib_cost`).

### Data pipeline (Mathlib measurement)

| Step | What it does |
|---|---|
| `Export.lean` | Dumps 771,129 constants with body sizes and citations to `data/graph.tsv` (~660 MB, gitignored; ~11 min) |
| `Flags.lean` | Instance, projection and class flags plus statement sizes to `data/flags.tsv` (gitignored) |
| `analyze.py` | Writes `data/results.json` and `visible.tsv` (gitignored) |
| `robustness.py` | Robustness checks |
| `paper_stats.py` | Every number in the paper, plus the figure data `data/fig_*.dat` |

### Main empirical findings

- Unfolded size grows about 1.5× per dependency level (R² = 0.98) and reaches about
  10^65.6.
- Reuse alone rediscovers the textbook core (`Set`, `Category`, `Functor`, …).
- **Two axes of human taste:**
  - curriculum concepts are predicted by reuse (AUC 0.88, 0.87 within the same file);
  - famous theorems are predicted by depth (AUC 0.78, 0.66 within the same file).
- **Negative result:** the product of the two factors does *not* predict human labels
  (AUC 0.62, against 0.73 for reuse alone).
- **Glue layer:** instances and projections are 12% of constants but receive 60% of
  citations, like function words in language and currency metabolites in metabolism.
- Mathlib obeys Zipf's law of abbreviation: definition names shorten with use.

## 4. `problem-atlas/`: ranking of 100 hard open problems

`atlas.pdf` (12 pages) ranks 100 open problems into four tiers: beyond Fields, Fields-level, major
breakthrough, and strong research. Each problem has a difficulty score and a raw-reasoning fit score. The atlas
also contains:
- a heat map of difficulty against fit;
- the problems that fell between 2013 and 2025;
- the barriers that block whole families of methods;
- odds estimates and suggested targets.

**Update, 9 Oct 2026:** cross-referenced against `github.com/openai/math` (released 6 Oct 2026: 372 claimed
result families, 3 papers withdrawn the next day). 30 of the 100 atlas problems now carry an AI claim.
- **Our picks with no AI claim:** union-closed sets, Černý, 1/3–2/3, Erdős–Gyárfás, sunflower, Erdős–Hajnal.
- **New suggested niche:** audit a claimed result. Check that its Lean statement really is the conjecture, find
  any gap, and write the short human proof.

## Open threads (to resume later)

1. **Lucas conjecture (our own; not found in the literature).** The maximum unfolded size
   at named cost `3m` is `2L_m-2`, so the speed limit is φ^(1/3).
   - **Known so far:**
     - Proved bracket: φ^(1/3) ≤ rate ≤ 5/4.
     - Exact search confirms the conjecture for `4 ≤ m ≤ 15`.
     - No linear potential can certify a rate below 1.2198 (LP duality).
     - Decoupled relaxations overshoot: about 1.179, departing from cost 33.
     - **Proved by hand (not yet in Lean):** the rate is exactly φ^(1/3) when every result
       cites at most 2 others: `u < 7·φ^(C/3)`. The proof uses greedy dominance plus the
       potential `max(z + z'/φ, φ^(1/3) z)`; see `notes/attempt.pdf`.
   - **Next steps:**
     1. Formalize the binary theorem in Lean.
     2. Try block amortization ("run of copies, then the window step that exploits it")
        for windows of size at most 3.
     3. Possibly a finite closed family of potential pieces on *reachable* states.
2. **Frege vs Extended Frege.** A famous open problem (Cook–Reckhow, 1979). Not
   attempted, and no progress claimed. It is explained in `notes/where_we_are.pdf` and
   `notes/attempt.pdf`.
3. **Paper restructuring (agreed direction).** Split into two papers:
   - (A) a theory paper: calculus of naming, speed limit, Lucas conjecture, complexity of
     optimal naming (target: NP-hardness), and the speed limit with citation
     multiplicities (expected 3^(1/3));
   - (B) an empirical Mathlib paper.
4. **Not done yet:**
   - the delayed-reward experiment on Mathlib's git history (does early reuse predict late
     reuse?);
   - rediscovering concepts by stripping names and running library learning;
   - a specialist literature check for novelty (path-count extremal problem; submodularity
     of inlining).
