# Mathematics without human understanders (draft)

A Lean-checked model of two claims:

- **T1 (formalism):** an artifact is valid mathematics regardless of who produced it and
  whether any human understands it.
- **T2 (trust transfer):** after enough verified successes, deferring to a superhumanly
  reliable agent can rationally outweigh deferring to human experts. Where the threshold sits
  in practice is a psychological and social "fuzzy boundary".

- `TrustThesis.lean` contains 16 results: the Hilbert vs. Thurston definitions, the trusted
  base of a checked proof, independent statement audits, Bayesian trust transfer, the limits of
  transfer to uncheckable domains, and the gradual-replacement dilemma for "what is a human".
- `paper/paper.pdf` (source in `paper/paper.tex`) is the first draft of the paper.

The file checks with Lean 4 + Mathlib, with no `sorry`. Axioms used are at most `propext`,
`Classical.choice` and `Quot.sound`. To check it, run this from any Mathlib project:

    lake env lean TrustThesis.lean

Lean certifies only that each conclusion follows from its stated hypotheses. The
philosophical content is in the hypotheses, which the paper lists and discusses.
