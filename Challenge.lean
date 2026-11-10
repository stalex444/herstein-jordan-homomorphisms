module
public import Mathlib

@[expose] public section
/-!
# Herstein's theorem: Jordan homomorphisms onto prime rings

An additive map `φ : R → S` between associative rings is a *Jordan homomorphism* when it respects
the symmetrized product: `φ (a * b + b * a) = φ a * φ b + φ b * φ a`. Homomorphisms and
anti-homomorphisms (`φ (a * b) = φ b * φ a`) are Jordan homomorphisms. Herstein's theorem is the
converse onto a prime ring: a Jordan homomorphism onto a prime ring of characteristic different
from 2 is a homomorphism or an anti-homomorphism (I. N. Herstein, Trans. Amer. Math. Soc. 81
(1956), Theorem H, with characteristic 3 also excluded; M. F. Smiley, Trans. Amer. Math. Soc. 84
(1957), p. 428, without that exclusion). This entry compares exactly these five statements.
Statements 1 and 2 are theorems of the 1950s and statements 3–5 are standard examples; nothing
here is a new theorem.

Vocabulary. No definition is added: every hypothesis is written out. Rings are `NonUnitalRing`
(associative, identity not required). `S` is *prime* when
`∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0` (the definition in Herstein's paper); `S` has
*no 2-torsion* when `∀ x : S, x + x = 0 → x = 0` (how Herstein and Smiley write "characteristic
different from 2").

The theorem:

1. `jordan_onto_prime` — a Jordan homomorphism `φ : R →+ S` onto a prime ring `S` without
   2-torsion satisfies `∀ a b, φ (a * b) = φ a * φ b` or `∀ a b, φ (a * b) = φ b * φ a`.
   The headline. This is Smiley's theorem as he states it: an additive map of rings, no identity
   assumed, and `2a = 0` implies `a = 0` in the target.

The domain form:

2. `twoIdentity_into_domain` — an additive map that preserves squares and the triple product,
   `φ (a * a) = φ a * φ a` and `φ (a * b * a) = φ a * φ b * φ a`, into a ring without zero
   divisors is multiplicative or anti-multiplicative. No surjectivity and no hypothesis on 2.
   This is Theorem 2 of N. Jacobson and C. E. Rickart (Trans. Amer. Math. Soc. 69 (1950),
   p. 482), with their definition of a Jordan homomorphism (the two identities). A Jordan
   homomorphism in the sense of statement 1 into a ring without 2-torsion satisfies both
   identities (proved in the library, not compared), so statement 2 covers that case as well.

Each hypothesis of statement 1 is needed. Each of the next three statements asserts that one
hypothesis fails, that the others hold, and that the map is neither multiplicative nor
anti-multiplicative:

3. `onto_needed` — not onto: there is a Jordan homomorphism from the `2 × 2` integer matrices
   into the `4 × 4` integer matrices (indexed by `Fin 2 ⊕ Fin 2`; a prime ring without
   2-torsion) that is not onto and is neither. The witness in the proof is `a ↦ diag(a, aᵀ)`.
4. `prime_needed` — target not prime: there is a Jordan homomorphism from pairs of `2 × 2`
   integer matrices onto pairs of `2 × 2` integer matrices (not a prime ring; no 2-torsion) that
   is neither. The witness in the proof is `(a, b) ↦ (a, bᵀ)`.
5. `two_needed` — 2-torsion: there is a Jordan homomorphism from `𝔽₂ × 𝔽₂` onto the field `𝔽₂`
   (a prime ring with 2-torsion) that is neither. The witness in the proof is `(x, y) ↦ x + y`.
   In a commutative ring with `x + x = 0` both sides of the identity of statement 1 are zero, so
   every additive map between such rings satisfies it. The witness preserves squares and does
   not satisfy the triple identity of statement 2.

The examples are standard. The maps of 3 and 4 put a homomorphism and an anti-homomorphism side
by side (`A ↦ (A, Aᵀ)` in Brešar, Math. Proc. Cambridge Philos. Soc. 144 (2008), §2;
`(A₁, A₂) ↦ (A₁, A₂ᵀ)` in Havlicek, arXiv:2004.00886v2, footnote 17), and 5 is an instance of
the degeneracy in characteristic 2 noted in Havlicek's footnote 15.

Sources and proof. The proof of statement 1 is not Smiley's, which goes through a lemma on prime
rings in which every commutator squares to zero. It follows Beidar, Brešar and Chebotar (Comm.
Algebra 31 (2003), Proposition 3.1, after Brešar 1989), who write for algebras over a ring
containing `1/2` and remark that their arguments also work in rings of characteristic not 2; the
key identity is Smiley's (7), p. 427. The proof of statement 2 is Jacobson and Rickart's: their
identity (7) and a lemma they attribute to Hua. The papers of 1950, 1956 and 1957 were read in
Internet Archive copies of the publisher's PDFs.

Not formalized. Characteristic 2: Smiley's remark (Added in proof, p. 429) that the two
identities of statement 2 may replace the hypothesis on 2 in his theorem is not proved here; the
library's two-identity form of statement 1 still assumes no 2-torsion. Semiprime targets (Baxter
and Martindale 1979; Brešar 1989) are not treated. Nor are the theorems that write a Jordan
homomorphism of a matrix ring or an operator algebra as a sum of a homomorphism and an
anti-homomorphism (Jacobson–Rickart; Kadison), nor anything about `*`-preserving maps.

Prior formalization. The case of complex-linear maps between unital complex algebras is
formalized in `github.com/openai/math` (`lean/OAI/Analysis/KadisonKastler/Jordan.lean`, theorem
`OAI.KadisonKastler.PreservesJordan.multiplicative_or_antimultiplicative`, first committed
2026-10-06). Statement 1 contains that case and is not limited to it. None of statements 2–5 was
found there (content search of its sources at commit 4eaee875, 2026-11-10).

Application (cited; no compared statement asserts it). The self-adjoint elements of an algebra
of observables are closed under the symmetrized product and not, in general, under the product
(Jordan, von Neumann and Wigner, 1934). Applied to the identity map, statement 1
says that on a prime ring without 2-torsion the symmetrized product determines the associative
product up to reversing the order of the factors: an associative product with the same
symmetrized product is the given product or its opposite. When the ring is not commutative
these are exactly two products.

Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with the
identical statement.
-/

namespace JordanPrime

open Matrix

/-- **1. Herstein's theorem, characteristic different from 2 (Smiley's form).** A Jordan
homomorphism onto a prime ring without 2-torsion is a homomorphism or an anti-homomorphism. -/
theorem jordan_onto_prime {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)
    (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  sorry

/-- **2. The domain form (Jacobson–Rickart, Theorem 2), in every characteristic.** An additive
map preserving squares and `a * b * a`, into a ring without zero divisors, is multiplicative or
anti-multiplicative. -/
theorem twoIdentity_into_domain {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hS : ∀ x y : S, x * y = 0 → x = 0 ∨ y = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  sorry

/-- **3. Surjectivity is needed.** A Jordan homomorphism that is not onto, into a prime ring
without 2-torsion, and is neither multiplicative nor anti-multiplicative. -/
theorem onto_needed :
    ∃ φ : Matrix (Fin 2) (Fin 2) ℤ →+ Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ,
      (∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a) ∧
      ¬ Function.Surjective φ ∧
      (∀ x y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ,
        (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) ∧
      (∀ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, x + x = 0 → x = 0) ∧
      (¬ ∀ a b, φ (a * b) = φ a * φ b) ∧ (¬ ∀ a b, φ (a * b) = φ b * φ a) := by
  sorry

/-- **4. Primeness is needed.** A Jordan homomorphism onto a ring that is not prime and has no
2-torsion; the map is neither multiplicative nor anti-multiplicative. -/
theorem prime_needed :
    ∃ φ : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ →+
        Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ,
      (∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a) ∧
      Function.Surjective φ ∧
      (¬ ∀ x y : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ,
        (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) ∧
      (∀ x : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ, x + x = 0 → x = 0) ∧
      (¬ ∀ a b, φ (a * b) = φ a * φ b) ∧ (¬ ∀ a b, φ (a * b) = φ b * φ a) := by
  sorry

/-- **5. The hypothesis on 2 is needed.** A Jordan homomorphism onto a prime ring with
2-torsion that is neither multiplicative nor anti-multiplicative. -/
theorem two_needed :
    ∃ φ : ZMod 2 × ZMod 2 →+ ZMod 2,
      (∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a) ∧
      Function.Surjective φ ∧
      (∀ x y : ZMod 2, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0) ∧
      (¬ ∀ x : ZMod 2, x + x = 0 → x = 0) ∧
      (¬ ∀ a b, φ (a * b) = φ a * φ b) ∧ (¬ ∀ a b, φ (a * b) = φ b * φ a) := by
  sorry

end JordanPrime
