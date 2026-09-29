# Reverse Involution in Isabelle/Isar

A structural-induction proof that reversing a list twice gives back the original
list, together with the three auxiliary lemmas it depends on. Each proof was
written by hand first, then transcribed to Isabelle/Isar and checked
mechanically — the handwritten pages are included, and every step in the theory
file matches a step on paper.

## Specification

Two recursive functions over the inductive list type, defined by `primrec`:

```isabelle
primrec cat :: "'a list ⇒ 'a list ⇒ 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list ⇒ 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"
```

## What is proved

| | Statement |
|---|---|
| `l1` | `cat` is associative |
| `l2` | `[]` is a right identity for `cat` |
| `l3` | `reverso` distributes over `cat`, reversing the order |
| `t1` | `reverso` is involutive: `reverso (reverso xs) = xs` |

`l3` uses `l1` and `l2`; the theorem `t1` uses `l3`.

## Proof style

The proofs are deliberately unautomated. Every one of the 27 steps is a single
rewrite by a single defining equation:

```isabelle
also have "... = x # cat (cat xs ys) zs" by (simp only: HI)
```

No `auto`, `simp` on its own, `blast`, `force`, `metis` or `arith`; no `sorry`
and no `oops`. The point is that the machine-checked proof has the same shape,
and the same justification on every line, as the one done on paper.

## Checking it yourself

With [Isabelle](https://isabelle.in.tum.de/) installed, put a `ROOT` file next
to the theory:

```
session T1 = HOL +
  theories
    T1_2026_2
```

then run:

```
isabelle build -D . -v
```

A clean run prints `Finished T1` and nothing else. Alternatively, open
`T1_2026_2.thy` in `isabelle jedit` — with continuous checking on, the overview
bar in the right margin stays clear when everything is proved.

## A note on the two missing steps

The handwritten proof of the theorem has ten steps in its inductive case; the
theory file has eight. The two that are absent are the ones justified *by
definition*, rewriting `[x]` into `x:[]`. On paper those are two different
notations and moving between them is a genuine step. In Isabelle `[x]` is merely
an abbreviation for `x # []`, resolved while the file is parsed, so both sides of
the step are literally the same term: the command would assert `t = t`, which a
calculational chain rejects (`Vacuous calculation result` mid-chain, and a lost
left endpoint if placed first). The two spots are marked with a comment in the
theory file.

## Files

- `T1_2026_2.thy` — the specification and the four Isar proofs
- `t1_provas.pdf` — the write-up, with the proofs in the calculational style
- `lemma1.png`, `lemma2.png`, `lemma3.png`, `teorema.png` — the handwritten proofs
- `Provamanualcompleta.png` — all four on one sheet

## Context

Coursework for Formal Methods (PUCRS, 2026/2). The write-up and the comments in
the theory file are in Portuguese.
