module
public import Mathlib

@[expose] public section
/-!
# Herstein's theorem: the proof library

An additive map `φ : R → S` between associative rings is a *Jordan homomorphism* when
`φ (a * b + b * a) = φ a * φ b + φ b * φ a`. This file proves Herstein's theorem in its
characteristic-not-two form: a Jordan homomorphism onto a prime ring without 2-torsion is
multiplicative or anti-multiplicative. Rings are not assumed to have an identity
(`NonUnitalRing`), and every hypothesis on the target is a plain `∀`-statement, so no new
typeclass is introduced.

The statement is Smiley's theorem (Trans. Amer. Math. Soc. 84 (1957), p. 428). The proof follows
the argument given in full by Beidar, Brešar and Chebotar (*Jordan superhomomorphisms*, Comm.
Algebra 31 (2003), Proposition 3.1, after Brešar 1989), there for algebras over a
ring containing `1/2`, with the remark that it also works in rings of characteristic not 2; that
ring-level argument is written out here. The domain form is Theorem 2 of Jacobson and Rickart
(Trans. Amer. Math. Soc. 69 (1950), p. 482), proved as they prove it.

Layout.

* The two-identity form of the definition, `φ (a * a) = φ a * φ a` and
  `φ (a * b * a) = φ a * φ b * φ a` (no hypothesis on 2). From it: the Jordan identity
  (`map_jordan_of_sq`), the linearized triple identity (`map_triple_lin`), `τ * ω = 0`
  (`defect_mul_defect`; Jacobson and Rickart's identity (7)), and
  `τ * φ r * ω + ω * φ r * τ = 0` (`defect_sandwich`; Smiley's identity (7)), where
  `τ = φ (a * b) - φ a * φ b` and `ω = φ (a * b) - φ b * φ a`.
* `map_sq_of_jordan`, `map_triple_of_jordan`: a Jordan homomorphism into a ring without
  2-torsion satisfies the two identities.
* `biadditive_cover`: two biadditive maps whose zero sets cover every pair; one of them vanishes.
  `mul_or_antimul_of_pairwise` applies it to the two defects.
* `mul_or_antimul_of_noZeroDivisors`: the two-identity form into a ring without zero divisors,
  in every characteristic and with no surjectivity.
* `mul_or_antimul_of_prime_of_twoIdentity`, `mul_or_antimul_of_prime`: the theorem, in the
  two-identity form (still assuming no 2-torsion) and for Jordan homomorphisms.

Primeness of matrix rings (`matrix_prime`) and the three examples are in
`HersteinJordanExamples.lean`.
-/

namespace HersteinJordan

open Matrix

section Core

variable {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)

/-! ### The two-identity form -/

/-- The Jordan identity from the square identity (linearization; no division). -/
theorem map_jordan_of_sq (hsq : ∀ a, φ (a * a) = φ a * φ a) (a b : R) :
    φ (a * b + b * a) = φ a * φ b + φ b * φ a := by
  have h := hsq (a + b)
  have e : (a + b) * (a + b) = a * a + (a * b + b * a) + b * b := by
    simp only [mul_add, add_mul]; abel
  have e' : (φ a + φ b) * (φ a + φ b) = φ a * φ a + (φ a * φ b + φ b * φ a) + φ b * φ b := by
    simp only [mul_add, add_mul]; abel
  rw [e] at h
  simp only [map_add] at h
  rw [hsq a, hsq b, e'] at h
  rw [map_add]
  exact add_left_cancel (add_right_cancel h)

/-- The linearized triple identity. -/
theorem map_triple_lin (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b c : R) :
    φ (a * b * c + c * b * a) = φ a * φ b * φ c + φ c * φ b * φ a := by
  have h := htri (a + c) b
  have e : (a + c) * b * (a + c) = a * b * a + (a * b * c + c * b * a) + c * b * c := by
    simp only [mul_add, add_mul]; abel
  have e' : (φ a + φ c) * φ b * (φ a + φ c) =
      φ a * φ b * φ a + (φ a * φ b * φ c + φ c * φ b * φ a) + φ c * φ b * φ c := by
    simp only [mul_add, add_mul]; abel
  rw [e] at h
  simp only [map_add] at h
  rw [htri a b, htri c b, e'] at h
  rw [map_add]
  exact add_left_cancel (add_right_cancel h)

/-- `τ * ω = 0`: the two defects of multiplicativity annihilate each other. -/
theorem defect_mul_defect (hsq : ∀ a, φ (a * a) = φ a * φ a)
    (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b : R) :
    (φ (a * b) - φ a * φ b) * (φ (a * b) - φ b * φ a) = 0 := by
  have h1 := hsq (a * b)
  have h2 := htri a (b * b)
  have h3 := hsq b
  have h4 := map_triple_lin φ htri (a * b) b a
  have e : a * b * b * a + a * b * (a * b) = a * b * (a * b) + a * (b * b) * a := by
    simp only [mul_assoc]; abel
  rw [e, map_add, h1, h2, h3] at h4
  have e' : (φ (a * b) - φ a * φ b) * (φ (a * b) - φ b * φ a) =
      (φ (a * b) * φ (a * b) + φ a * (φ b * φ b) * φ a) -
        (φ (a * b) * φ b * φ a + φ a * φ b * φ (a * b)) := by
    simp only [mul_sub, sub_mul, mul_assoc]; abel
  rw [e', h4, sub_self]

/-- The key identity (Smiley 1957, identity (7), p. 427):
`τ * φ r * ω + ω * φ r * τ = 0`. -/
theorem defect_sandwich (hsq : ∀ a, φ (a * a) = φ a * φ a)
    (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a) (a b r : R) :
    (φ (a * b) - φ a * φ b) * φ r * (φ (a * b) - φ b * φ a) +
      (φ (a * b) - φ b * φ a) * φ r * (φ (a * b) - φ a * φ b) = 0 := by
  have hJ := map_jordan_of_sq φ hsq a b
  rw [map_add] at hJ
  have hba : φ (b * a) = φ a * φ b + φ b * φ a - φ (a * b) := eq_sub_of_add_eq' hJ
  have hW1 : φ (a * (b * r * b) * a) = φ a * (φ b * φ r * φ b) * φ a := by rw [htri, htri]
  have hW2 : φ (b * (a * r * a) * b) = φ b * (φ a * φ r * φ a) * φ b := by rw [htri, htri]
  have hL := map_triple_lin φ htri (a * b) r (b * a)
  have e : a * b * r * (b * a) + b * a * r * (a * b) =
      a * (b * r * b) * a + b * (a * r * a) * b := by
    simp only [mul_assoc]
  rw [e, map_add, hW1, hW2, hba] at hL
  have e' : (φ (a * b) - φ a * φ b) * φ r * (φ (a * b) - φ b * φ a) +
      (φ (a * b) - φ b * φ a) * φ r * (φ (a * b) - φ a * φ b) =
      (φ a * (φ b * φ r * φ b) * φ a + φ b * (φ a * φ r * φ a) * φ b) -
        (φ (a * b) * φ r * (φ a * φ b + φ b * φ a - φ (a * b)) +
          (φ a * φ b + φ b * φ a - φ (a * b)) * φ r * φ (a * b)) := by
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc]; abel
  rw [e', hL, sub_self]

/-! ### From the Jordan identity to the two identities -/

/-- A Jordan homomorphism into a ring without 2-torsion preserves squares. -/
theorem map_sq_of_jordan (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (h2 : ∀ x : S, x + x = 0 → x = 0) (a : R) : φ (a * a) = φ a * φ a := by
  have h := hJ a a
  rw [map_add] at h
  refine sub_eq_zero.mp (h2 _ ?_)
  have : φ (a * a) - φ a * φ a + (φ (a * a) - φ a * φ a) =
      (φ (a * a) + φ (a * a)) - (φ a * φ a + φ a * φ a) := by abel
  rw [this, h, sub_self]

/-- A Jordan homomorphism into a ring without 2-torsion preserves `a * b * a`. -/
theorem map_triple_of_jordan (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (h2 : ∀ x : S, x + x = 0 → x = 0) (a b : R) : φ (a * b * a) = φ a * φ b * φ a := by
  have hsq := map_sq_of_jordan φ hJ h2
  have h := hJ a (a * b + b * a)
  have h' := hJ (a * a) b
  have e : a * (a * b + b * a) + (a * b + b * a) * a =
      (a * a * b + b * (a * a)) + (a * b * a + a * b * a) := by
    simp only [mul_add, add_mul, mul_assoc]; abel
  rw [e, map_add, h', hsq, hJ, map_add] at h
  refine sub_eq_zero.mp (h2 _ ?_)
  have : φ (a * b * a) - φ a * φ b * φ a + (φ (a * b * a) - φ a * φ b * φ a) =
      (φ a * φ a * φ b + φ b * (φ a * φ a) + (φ (a * b * a) + φ (a * b * a))) -
        (φ a * (φ a * φ b + φ b * φ a) + (φ a * φ b + φ b * φ a) * φ a) := by
    simp only [mul_add, add_mul, mul_assoc]; abel
  rw [this, h, sub_self]

end Core

/-! ### The covering argument -/

/-- Two biadditive maps whose zero sets cover every pair: one of them vanishes identically.
(An additive group is not the union of two proper subgroups, applied twice.) -/
theorem biadditive_cover {G H K : Type*} [AddGroup G] [AddGroup H] [AddGroup K]
    (f g : G → H → K)
    (fl : ∀ a a' b, f (a + a') b = f a b + f a' b) (fr : ∀ a b b', f a (b + b') = f a b + f a b')
    (gl : ∀ a a' b, g (a + a') b = g a b + g a' b) (gr : ∀ a b b', g a (b + b') = g a b + g a b')
    (h : ∀ a b, f a b = 0 ∨ g a b = 0) :
    (∀ a b, f a b = 0) ∨ (∀ a b, g a b = 0) := by
  -- first in the second variable, for a fixed `a`
  have row : ∀ a, (∀ b, f a b = 0) ∨ (∀ b, g a b = 0) := by
    intro a
    by_contra hc
    push Not at hc
    obtain ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ := hc
    have hgb : g a b = 0 := (h a b).resolve_left hb
    have hfb' : f a b' = 0 := (h a b').resolve_right hb'
    rcases h a (b + b') with h0 | h0
    · rw [fr, hfb', add_zero] at h0; exact hb h0
    · rw [gr, hgb, zero_add] at h0; exact hb' h0
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, b, hab⟩, ⟨a', b', hab'⟩⟩ := hc
  have hga : ∀ b, g a b = 0 := (row a).resolve_left (fun hf => hab (hf b))
  have hfa' : ∀ b, f a' b = 0 := (row a').resolve_right (fun hg => hab' (hg b'))
  rcases row (a + a') with h0 | h0
  · have := h0 b; rw [fl, hfa' b, add_zero] at this; exact hab this
  · have := h0 b'; rw [gl, hga b', zero_add] at this; exact hab' this

section Theorems

variable {R S : Type*} [NonUnitalRing R] [NonUnitalRing S] (φ : R →+ S)

/-- From "for each pair, one defect vanishes" to "one defect vanishes identically". -/
theorem mul_or_antimul_of_pairwise
    (h : ∀ a b, φ (a * b) - φ a * φ b = 0 ∨ φ (a * b) - φ b * φ a = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  rcases biadditive_cover (fun a b => φ (a * b) - φ a * φ b) (fun a b => φ (a * b) - φ b * φ a)
      (fun a a' b => by simp only [add_mul, map_add]; abel)
      (fun a b b' => by simp only [mul_add, map_add]; abel)
      (fun a a' b => by simp only [add_mul, mul_add, map_add]; abel)
      (fun a b b' => by simp only [add_mul, mul_add, map_add]; abel) h with h | h
  · exact Or.inl fun a b => sub_eq_zero.mp (h a b)
  · exact Or.inr fun a b => sub_eq_zero.mp (h a b)

/-- **The domain form, in every characteristic** (two-identity definition; no surjectivity).
An additive map that preserves squares and `a * b * a`, into a ring without zero divisors, is
multiplicative or anti-multiplicative. -/
theorem mul_or_antimul_of_noZeroDivisors
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hS : ∀ x y : S, x * y = 0 → x = 0 ∨ y = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  mul_or_antimul_of_pairwise φ fun a b => hS _ _ (defect_mul_defect φ hsq htri a b)

/-- The two-identity form of the theorem: onto a prime ring without 2-torsion. -/
theorem mul_or_antimul_of_prime_of_twoIdentity
    (hsq : ∀ a, φ (a * a) = φ a * φ a) (htri : ∀ a b, φ (a * b * a) = φ a * φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  refine mul_or_antimul_of_pairwise φ fun a b => ?_
  set τ := φ (a * b) - φ a * φ b with hτ
  set ω := φ (a * b) - φ b * φ a with hω
  have key : ∀ x : S, τ * x * ω + ω * x * τ = 0 := by
    intro x
    obtain ⟨r, rfl⟩ := hsurj x
    exact defect_sandwich φ hsq htri a b r
  have quad : ∀ x y : S, τ * x * (ω * y * τ) = 0 := by
    intro x y
    refine h2 _ ?_
    have kx := key x
    have ky := key y
    have kc := key (x * τ * y)
    -- τ x (ω y τ) = -τ x (τ y ω) = ω (x τ y) τ = -(τ x ω) y τ
    have e : τ * x * (ω * y * τ) + τ * x * (ω * y * τ) =
        τ * x * (τ * y * ω + ω * y * τ) - (τ * (x * τ * y) * ω + ω * (x * τ * y) * τ) +
          (τ * x * ω + ω * x * τ) * y * τ := by
      simp only [mul_add, add_mul, mul_assoc]; abel
    rw [e, ky, kc, kx]
    simp
  by_cases hτ0 : τ = 0
  · exact Or.inl hτ0
  · right
    have h1 : ∀ y : S, ω * y * τ = 0 := fun y =>
      (hprime τ (ω * y * τ) fun x => quad x y).resolve_left hτ0
    exact (hprime ω τ h1).resolve_right hτ0

/-- **Herstein's theorem, characteristic-not-two form.** A Jordan homomorphism onto a prime ring
without 2-torsion is multiplicative or anti-multiplicative. -/
theorem mul_or_antimul_of_prime
    (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hprime : ∀ x y : S, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    (h2 : ∀ x : S, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) :=
  mul_or_antimul_of_prime_of_twoIdentity φ (map_sq_of_jordan φ hJ h2)
    (map_triple_of_jordan φ hJ h2) hsurj hprime h2

end Theorems

end HersteinJordan
