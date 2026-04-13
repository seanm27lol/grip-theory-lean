/-
# Grip Theory — Puzzle State Space

The state of a puzzle is described by a function `a : P → G` assigning
to each piece `X ∈ P` its attitude `a(X) ∈ G`. The state space
admits a group structure (a subgroup of the wreath product `G ≀_P S_P`).

Given attitudes `a, b : P → G`, their product is defined by:
  `(ab)(X) = a(X) · b(X · a(X))`

Reference: https://hypercubing.xyz/theory/grip-theory/
-/

import Mathlib

universe u v

open MulAction Set Pointwise

variable {Γ : Type u} {G : Type v} [Group G] [MulAction G Γ]

/-! ## Puzzle State as Attitude Function

A puzzle state is a function assigning to each piece (identified by its
solved grip set) an attitude (an element of the grip group).

The group operation on puzzle states is:
  `(a * b)(X) = a(X) * b(X • a(X))`
where `X • g` denotes the pointwise action of `g` on the set `X`.
-/

/-- A puzzle state for a grip system with grip group `G` acting on grips `Γ`,
    with piece set `P`. It assigns an attitude to each piece. -/
structure PuzzleState (Γ : Type u) (G : Type v) [Group G] [MulAction G Γ]
    (P : Set (Set Γ)) where
  /-- The attitude function: for each piece (solved grip set), its current attitude. -/
  attitude : Set Γ → G
  /-- Active grips stay within the piece set. -/
  active_in_pieces : ∀ X ∈ P, (attitude X) • X ∈ P

/-- The solved (identity) state. -/
def PuzzleState.solved {P : Set (Set Γ)}
    (hP : ∀ X ∈ P, (1 : G) • X ∈ P) : PuzzleState Γ G P where
  attitude := fun _ => 1
  active_in_pieces := hP

/-
The identity action preserves every set.
-/
theorem one_smul_set_mem {P : Set (Set Γ)} (hP : ∀ X ∈ P, X ∈ P) :
    ∀ X ∈ P, (1 : G) • X ∈ P := by
  -- The identity element in a group acts as the identity function on any set.
  simp [one_smul]

/-! ## The Permutation View

A puzzle state can also be viewed as a permutation `π : P → P` together
with an attitude at each position, such that `π(X) = a(X) • X`.
-/

/-- The permutation induced by a puzzle state: `π(X) = a(X) • X`. -/
def PuzzleState.perm {P : Set (Set Γ)}
    (s : PuzzleState Γ G P) (X : Set Γ) : Set Γ :=
  s.attitude X • X

/-! ## Orbit Decomposition

The state space decomposes as a product over orbits of the action on pieces:
  `G ≀ P ≅ ∏_{O ∈ P/G} Stab(Y ∈ O) ≀_O S_O`

This means piece types are independent: the state of corners is independent
of the state of edges, etc.
-/

/-- The orbit of a piece under the grip group action on `Set Γ`. -/
def pieceOrbit (X : Set Γ) : Set (Set Γ) :=
  MulAction.orbit G X

/-
Two pieces in the same orbit have conjugate stabilizers.
-/
theorem stabilizer_conjugate_of_orbit {X Y : Set Γ} {g : G} (h : g • X = Y) :
    MulAction.stabilizer G Y =
      (MulAction.stabilizer G X).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  -- By definition of conjugation, we have that for any $h \in G$, $h \in \text{stabilizer}(Y)$ if and only if $g^{-1}hg \in \text{stabilizer}(X)$.
  have h_conj : ∀ h : G, h ∈ stabilizer G Y ↔ g⁻¹ * h * g ∈ stabilizer G X := by
    simp_all +decide [ ← h, ← Set.mem_inv, ← mul_assoc, stabilizerSubmonoid ];
    simp +decide [ ← Set.mem_smul_set_iff_inv_smul_mem, mul_smul, inv_smul_smul ];
    simp +decide [ inv_smul_eq_iff ];
  ext h; simp_all +decide [ Subgroup.mem_map, mul_assoc ] ;
  refine' ⟨ fun hh => ⟨ g⁻¹ * ( h * g ), hh, by group ⟩, _ ⟩ ; rintro ⟨ x, hx, rfl ⟩ ; simp_all +decide [ mul_assoc ] ;