# Herstein's theorem: Jordan homomorphisms onto prime rings

Kernel-checked, in Lean 4 + Mathlib. An additive map `φ : R → S` between associative rings is a
**Jordan homomorphism** when it respects the symmetrized product,
`φ(ab + ba) = φ(a)φ(b) + φ(b)φ(a)`. Homomorphisms and anti-homomorphisms (`φ(ab) = φ(b)φ(a)`) are
Jordan homomorphisms. **Herstein's theorem** is the converse onto a prime ring: a Jordan
homomorphism onto a prime ring of characteristic different from 2 is a homomorphism or an
anti-homomorphism. This repository proves it as Smiley states it (additive maps of rings, no
identity assumed, no 2-torsion in the target), proves the domain form of Jacobson and Rickart in
every characteristic, and gives one example for each hypothesis showing that it cannot be dropped.

Statements 1 and 2 formalize prior work (Herstein 1956 and Smiley 1957; Jacobson and Rickart
1950). Statements 3–5 are standard examples. Nothing here is a new theorem. A formalization of
the complex-linear case of statement 1 already exists; see "Prior formalization" below.

## The compared statements (namespace `JordanPrime`)

No definition is added; every hypothesis is written out. Rings are `NonUnitalRing`. `S` is *prime*
when `∀ x y, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0`, and has *no 2-torsion* when
`∀ x, x + x = 0 → x = 0`.

| # | name | statement |
|---|------|-----------|
| 1 | `jordan_onto_prime` | a Jordan homomorphism `φ : R →+ S` onto a prime ring without 2-torsion is multiplicative or anti-multiplicative. The headline (Smiley 1957, p. 428). |
| 2 | `twoIdentity_into_domain` | an additive map with `φ(a²) = φ(a)²` and `φ(aba) = φ(a)φ(b)φ(a)` into a ring without zero divisors is multiplicative or anti-multiplicative; every characteristic, no surjectivity (Jacobson–Rickart 1950, Theorem 2) |
| 3 | `onto_needed` | surjectivity is needed: there is a Jordan homomorphism from `2 × 2` into `4 × 4` integer matrices (a prime ring without 2-torsion) that is not onto and is neither |
| 4 | `prime_needed` | primeness is needed: there is a Jordan homomorphism from pairs of `2 × 2` integer matrices onto pairs of `2 × 2` integer matrices (not prime, no 2-torsion) that is neither |
| 5 | `two_needed` | the hypothesis on 2 is needed: there is a Jordan homomorphism from `𝔽₂ × 𝔽₂` onto `𝔽₂` (prime, with 2-torsion) that is neither |

Statements 3–5 are existence statements. Each asserts that one hypothesis fails, that the others
hold, and that the conclusion fails. The witnesses in the proofs are
`HersteinJordan.blockTranspose` (`a ↦ diag(a, aᵀ)`), `sndTranspose` (`(a, b) ↦ (a, bᵀ)`) and
`sumMod2` (`(x, y) ↦ x + y`). Every compared theorem depends on `propext`, `Classical.choice` and
`Quot.sound` only.

## The proof in five steps

Write `τ = φ(ab) − φ(a)φ(b)` and `ω = φ(ab) − φ(b)φ(a)`.

1. In a ring without 2-torsion the Jordan identity gives `φ(a²) = φ(a)²` and
   `φ(aba) = φ(a)φ(b)φ(a)` (cancel a 2 each time).
2. Linearizing: `φ(abc + cba) = φ(a)φ(b)φ(c) + φ(c)φ(b)φ(a)`.
3. Evaluating `φ(ab·r·ba + ba·r·ab)` by step 1 (as `a(brb)a + b(ara)b`) and by step 2, with the
   Jordan identity for `φ(ba)`, gives `τ φ(r) ω + ω φ(r) τ = 0` for every `r` (Smiley's identity
   (7)). Given the two identities of step 1, no hypothesis on 2 or on the target is used here.
4. If `φ` is onto, `τ x ω + ω x τ = 0` for every `x` in the target. Three uses of this give
   `2·τ x ω y τ = 0`, so `τ x ω y τ = 0` for all `x, y`, and primeness (twice) gives `τ = 0` or
   `ω = 0`, for each pair `(a, b)`.
5. `τ` and `ω` are additive in `a` and in `b`, and an additive group is not the union of two proper
   subgroups; applied twice, one of them vanishes for all pairs.

For statement 2 the two identities of step 1 are the hypotheses; step 2 and `τ ω = 0` (Jacobson
and Rickart's identity (7)) follow from them; the absence of zero divisors gives `τ = 0` or
`ω = 0` for each pair; step 5 (their Lemma 1, which they attribute to Hua) finishes.

## Relation to the literature

- **The statements.** Statement 1 is the Theorem of Smiley, *Jordan homomorphisms onto prime
  rings*, Trans. Amer. Math. Soc. 84 (1957), 426–429, p. 428: a mapping of a ring onto a prime
  ring in which `2a = 0` implies `a = 0`. Theorem H of Herstein, *Jordan homomorphisms*, Trans.
  Amer. Math. Soc. 81 (1956), 331–341, p. 340, is the same with characteristic 3 also excluded;
  the element-wise definition of a prime ring used here is Herstein's (p. 334). Statement 2 is
  Theorem 2 of Jacobson and Rickart, *Jordan homomorphisms of rings*, Trans. Amer. Math. Soc. 69
  (1950), 479–502, p. 482, with their definition of a Jordan homomorphism (p. 479). These three
  papers were read on 2026-11-10 in Internet Archive copies of the publisher's PDFs (text
  extractions of the scans); the pages read are listed in `formalization.yaml`.
- **The proof of statement 1** is not Smiley's, which goes through a lemma on prime rings in
  which every commutator squares to zero. It follows Beidar, Brešar and Chebotar, *Jordan
  superhomomorphisms*, Comm. Algebra 31 (2003), 633–644, Proposition 3.1 (after Brešar, J.
  Algebra 127 (1989)). They write for algebras over a ring containing `1/2` and remark that their
  arguments also work in rings of characteristic not 2; here the maps are additive maps of rings
  and the last step cancels a 2 where they divide by 2. No novelty is claimed for the ring-level
  form, which is the setting of Smiley's theorem.
- **The proof of statement 2** is Jacobson and Rickart's.
- **The examples.** `A ↦ (A, Aᵀ)` is in Brešar, *Jordan homomorphisms revisited*, Math. Proc.
  Cambridge Philos. Soc. 144 (2008), 317–328, §2; `(A₁, A₂) ↦ (A₁, A₂ᵀ)` is in Havlicek,
  arXiv:2004.00886v2, footnote 17; the degeneracy of the identity in characteristic 2 is in
  Havlicek's footnote 15. Statements 3–5 are `2 × 2` integer and `𝔽₂` instances of these.
- **History.** Havlicek §4.2, for the sequence Hua, Jacobson–Rickart, Herstein, Yamaguti, Smiley,
  Baxter–Martindale, Brešar; Brešar (2008), introduction.

## Prior formalization

The case of complex-linear maps between unital complex algebras is formalized in
[`openai/math`](https://github.com/openai/math), file
`lean/OAI/Analysis/KadisonKastler/Jordan.lean`, theorem
`OAI.KadisonKastler.PreservesJordan.multiplicative_or_antimultiplicative` (first committed
2026-10-06). Statement 1 contains that case and is free of three restrictions: additive maps in
place of complex-linear ones, no identity element, and no 2-torsion in place of complex scalars.
That file also proves the complex-linear counterparts of the library lemmas for steps 1–3.
Statements 2–5 were not found there (all files searched by name and by content at commit
4eaee875, 2026-11-10).

Contact with that file. The proof plan was written from the Beidar–Brešar–Chebotar argument
before the file was found. An AI-assisted scope review then found the file, read all of it, and
compiled a scratch check modelled on it; that scratch is not in this repository and was not
opened when the Lean here was written. Before writing the Lean, the drafting session read the
scope review's report and lines 1–40 and 150–182 of the file (its header, definitions, first
lemma and main theorem with its proof); the rest was read after the build. Both developments
follow the same classical argument. No code was copied. `formalization.yaml` records this in
full, and records the relationship as "other", not "independent".

Two separate Lean developments are adjacent.
[`abderrahim-lectures/braided-sym-deriv`](https://github.com/abderrahim-lectures/braided-sym-deriv)
formalizes Jordan *derivations* (Brešar 1988; Herstein 1957). The registry entry
PALOMAR-2026-10-28-000031 (Colbrook and Stepaniants, spectral isometries of C*-algebras) proves
that certain maps are Jordan *isomorphisms* (square-preserving linear bijections) and that Jordan
derivations of semiprime complex algebras are derivations. Neither proves that a Jordan
homomorphism is a homomorphism or an anti-homomorphism.

No formalization of statement 1 for additive maps of rings, or of statements 2–5, was found on
2026-11-10 in: Mathlib (sources at the pin and at master 21fc68be; issue and pull-request
search); the Lean Zulip public channels; the Lean Reservoir package index; the Palomar registry
(search API); TauCeti and Lean Pool (sources); the repositories named above (sources); the titles
of all Archive of Formal Proofs entries; the abstracts of the Mizar Mathematical Library;
Metamath `set.mm`; HOL Light, MathComp and three Agda libraries (sources); and web and GitHub
repository searches. The contents of Archive of Formal Proofs entries and the coq-community
repositories were not searched. This is a dated search, not a claim of priority.

## Not formalized

- The theorem in characteristic 2: Smiley's remark (Added in proof, p. 429) that the two
  identities of statement 2 may replace the hypothesis on 2. The library's two-identity form of
  statement 1 still assumes no 2-torsion.
- Semiprime targets (Baxter–Martindale 1979; Brešar 1989).
- The theorems that write a Jordan homomorphism of a matrix ring or an operator algebra as a sum
  of a homomorphism and an anti-homomorphism (Jacobson–Rickart; Kadison).
- Anything about `*`-preserving maps, or about unitary and anti-unitary symmetries.

## Application (cited; no compared statement asserts it)

The self-adjoint elements of an algebra of observables are closed under the symmetrized product
and not, in general, under the product (the setting of Jordan, von Neumann and Wigner, 1934).
Applied to the identity map, statement 1 says that on a prime ring without 2-torsion the
symmetrized product determines the associative product up to reversing the order of the factors:
an associative product with the same symmetrized product is the given product or its opposite.
When the ring is not commutative these are exactly two products, a product and its opposite.

## Files

| file | content |
|------|---------|
| `Challenge.lean` | the five statements, unproved; imports Mathlib only |
| `Solution.lean` | the five statements, proved by transfer from the library |
| `HersteinJordan.lean` | the proof library: the identities, the covering lemma, and the theorems behind statements 1 and 2 (with the two-identity form of statement 1) |
| `HersteinJordanExamples.lean` | primeness of matrix rings, a matrix corollary, the three examples |
| `Axioms.lean` | `#print axioms` for the compared and library theorems |
| `comparator.json` | the compared names |
| `formalization.yaml` | registry metadata |
| `BUILD.txt`, `SHA256SUMS` | build record and file hashes |

## Build

Lean `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Developed with AI assistance (Anthropic Claude, in Claude Code) under the author's direction.
