import Mathlib

/-
# Problem Description

Throughout, fix an odd integer base `B > 3`.

This problem concerns Kaprekar's routine applied to `4`-tuples of base-`B` digits.
Given a `4`-tuple of base-`B` digits, sort them as `a₁ ≥ a₂ ≥ a₃ ≥ a₄` (each
`aᵢ ∈ {0, 1, …, B-1}`). Kaprekar's operation forms the descending number
`a₁a₂a₃a₄` and the ascending number `a₄a₃a₂a₁` in base `B` and subtracts them.
Their difference equals

  `(a₁ B³ + a₂ B² + a₃ B + a₄) - (a₄ B³ + a₃ B² + a₂ B + a₁)
    = d₁ (B³ - 1) + d₂ (B² - B)`,

where `d₁ = a₁ - a₄` and `d₂ = a₂ - a₃`. Hence the next iterate depends only on the
pair `(d₁, d₂)`, justifying the use of difference pairs as states.

We study the dynamical system given by Kaprekar's map on the space of difference
pairs, its terminal cycles, and a conjugacy with a "doubling map" on projective
residues.

## Notes and Interpretation

- All claims were checked computationally for odd bases `B` up to `39`.
- The bound `c_max(B) ≤ (B-1)/2` holds for all tested `B`, with equality exactly for
  `B ∈ {7, 11, 13, 19, 23, 29, 37}` in this range — precisely the primes `≥ 7` for
  which `2` has projective order `(B-1)/2` (the least `m` with `2^m ≡ ±1 mod B`).
- The map `Φ` realizes the dynamics of `K_B` on `T_B` as multiplication by `2` on
  (unordered pairs of) projective residues.
- "`4`-digit" allows leading zeros: states are arbitrary multisets of four base-`B`
  digits with `d₁ ≥ 1`.
-/

/-! ## Auxiliary definitions for digits and sorting -/

/-- Sort four natural numbers in descending order, returning the `4`-tuple
`(b₁, b₂, b₃, b₄)` with `b₁ ≥ b₂ ≥ b₃ ≥ b₄`. -/
def sort4 (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match (List.mergeSort [a, b, c, d] (· ≥ ·)) with
  | [x, y, z, w] => (x, y, z, w)
  | _ => (0, 0, 0, 0)

/-! ## Main Definitions -/

/-- **Definition 2 (State space `X_B`).**
`X_B = {(d₁, d₂) ∈ ℕ² : 1 ≤ d₁ < B, 0 ≤ d₂ ≤ d₁}`.
The constraint `d₁ ≥ 1` excludes the trivial repdigit case `a₁ = a₂ = a₃ = a₄`. -/
def XBset (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter (fun p => 1 ≤ p.1 ∧ p.1 < B ∧ p.2 ≤ p.1)

/-- **Definition 3 (Kaprekar map `K_B`).**
For `(d₁, d₂)`, set `N = d₁ (B³ - 1) + d₂ (B² - B)`, take the four base-`B` digits
`(c₁, c₂, c₃, c₄)` of `N` (with `N = c₁ B³ + c₂ B² + c₃ B + c₄`), sort them as
`b₁ ≥ b₂ ≥ b₃ ≥ b₄`, and return `(b₁ - b₄, b₂ - b₃)`. -/
def KB (B : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let N := p.1 * (B ^ 3 - 1) + p.2 * (B ^ 2 - B)
  match sort4 (N / B ^ 3) ((N / B ^ 2) % B) ((N / B) % B) (N % B) with
  | (b1, b2, b3, b4) => (b1 - b4, b2 - b3)

/-- **Definition 4 (Target set `T_B`).**
`T_B = {(d₁, d₂) ∈ X_B : d₁ > d₂ > 0, d₁ odd, d₂ odd}`. -/
def TBset (B : ℕ) : Finset (ℕ × ℕ) :=
  (XBset B).filter (fun p => p.2 < p.1 ∧ 0 < p.2 ∧ Odd p.1 ∧ Odd p.2)

/-- The setoid on `ZMod B` identifying each residue with its negative (`x ∼ -x`). -/
def projSetoid (B : ℕ) : Setoid (ZMod B) where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y h; rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; ring)
    · intro x y z hxy hyz
      rcases hxy with h1 | h1 <;> rcases hyz with h2 | h2
      · exact Or.inl (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inl (by rw [h1, h2]; ring)

/-- **Definition 5 (Projective residues `P_B`).**
`P_B = (ZMod B) / {±1}`. (The nonzero projective residues
`((ZMod B) \ {0}) / {±1}` are those classes different from the class of `0`.) -/
def PB (B : ℕ) := Quotient (projSetoid B)

/-- The projective class `[x]` of `x : ZMod B`. -/
def PBmk (B : ℕ) (x : ZMod B) : PB B := Quotient.mk (projSetoid B) x

/-- The unordered pairs of distinct nonzero projective residues, i.e. `binom(P_B, 2)`.
An element of `Sym2 (P_B)` lies in this set iff it is not on the diagonal (its two
entries are distinct) and the class `[0]` is not one of its entries. -/
def binomSet (B : ℕ) : Set (Sym2 (PB B)) :=
  {s | ¬ s.IsDiag ∧ PBmk B 0 ∉ s}

/-- **Definition 6 (The map `Φ`).**
For `(d₁, d₂)` (with `d₁, d₂` both odd, as in `T_B`), set `r = (d₁ + d₂)/2` and
`s = (d₁ - d₂)/2`, and return the unordered pair `{[r], [s]}` of projective residues. -/
def Phi (B : ℕ) (p : ℕ × ℕ) : Sym2 (PB B) :=
  Sym2.mk (PBmk B (((p.1 + p.2) / 2 : ℕ) : ZMod B), PBmk B (((p.1 - p.2) / 2 : ℕ) : ZMod B))

/-- Doubling on projective residues: `[x] ↦ [2x]`. Well-defined since `2(-x) = -(2x)`. -/
def doubleP (B : ℕ) : PB B → PB B :=
  Quotient.map (fun x => 2 * x) (by
    intro x y h
    rcases h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h]; ring))

/-- **Definition 7 (Doubling map `D`).**
`D({[r], [s]}) = {[2r], [2s]}`, the image of the unordered pair under `[·] ↦ [2·]`. -/
def Dmap (B : ℕ) : Sym2 (PB B) → Sym2 (PB B) := Sym2.map (doubleP B)

/-- The number of terminal cycles of `K_B` of length exactly `c_max(B)`.
A terminal cycle is the orbit of a periodic point; its length is the minimal period.
Counting the periodic points whose minimal period equals `c_max(B)` and dividing by
`c_max(B)` (the number of points per such cycle) gives the number of such cycles. -/
noncomputable def cmax (B : ℕ) : ℕ :=
  (XBset B).sup (fun p => Function.minimalPeriod (KB B) p)

/-- Number of terminal cycles of `K_B` whose length equals `c_max(B)`. -/
noncomputable def numMaxCycles (B : ℕ) : ℕ :=
  ((XBset B).filter (fun p => Function.minimalPeriod (KB B) p = cmax B)).card / cmax B

/-! ## Main Statements -/

/-- **Statement 1 (Theorem 1, structural).**
Let `B > 3` be odd. Then:
1. `K_B(T_B) ⊆ T_B`;
2. `K_B³(X_B) ⊆ T_B`;
3. `Φ : T_B → binom(P_B, 2)` is a bijection;
4. the restriction `K_B : T_B → T_B` is conjugate, under `Φ`, to the doubling map `D`,
   i.e. `Φ(K_B(d₁, d₂)) = D(Φ(d₁, d₂))` for all `(d₁, d₂) ∈ T_B`. -/
theorem thm_structural (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    -- (1) `K_B` maps `T_B` into `T_B`
    (∀ p ∈ TBset B, KB B p ∈ TBset B) ∧
    -- (2) the third iterate of `K_B` maps `X_B` into `T_B`
    (∀ p ∈ XBset B, (KB B)^[3] p ∈ TBset B) ∧
    -- (3) `Φ` is a bijection from `T_B` onto `binom(P_B, 2)`
    (Set.BijOn (Phi B) (↑(TBset B)) (binomSet B)) ∧
    -- (4) conjugacy with the doubling map
    (∀ p ∈ TBset B, Phi B (KB B p) = Dmap B (Phi B p)) := by
  sorry

/-- **Statement 2 (Corollary 1, cycle-length bound).**
Let `B > 3` be odd. Then `c_max(B) ≤ (B-1)/2`. Moreover equality holds if and only if
`B ≥ 7`, `B` is prime, and the least positive integer `m` with `2^m ≡ ±1 (mod B)` is
`m = (B-1)/2`. -/
theorem cor_length (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) :
    cmax B ≤ (B - 1) / 2 ∧
    (cmax B = (B - 1) / 2 ↔
      (7 ≤ B ∧ B.Prime ∧
        IsLeast {m : ℕ | 0 < m ∧ ((2 : ZMod B) ^ m = 1 ∨ (2 : ZMod B) ^ m = -1)}
          ((B - 1) / 2))) := by
  sorry

/-- **Statement 3 (Corollary 2, count of maximal cycles).**
Suppose `B` is a prime `p` for which equality holds in Statement 2
(so `c_max(p) = (p-1)/2`). Then the number of terminal cycles of `K_p` of length
exactly `c_max(p)` equals `⌊(c_max(p) - 1)/2⌋`. -/
theorem cor_prime (B : ℕ) (hB3 : 3 < B) (hBodd : Odd B) (hBprime : B.Prime)
    (hEq : cmax B = (B - 1) / 2) :
    numMaxCycles B = (cmax B - 1) / 2 := by
  sorry