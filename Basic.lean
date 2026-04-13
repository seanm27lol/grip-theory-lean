/-
# Grip Theory — Basic Definitions

Grip theory is a framework for analyzing twisty puzzles (like Rubik's cube)
in a geometry-independent way. It was first developed on the TwistyPuzzles forum
in 2009.

Reference: https://hypercubing.xyz/theory/grip-theory/

## Overview

A **grip system** consists of:
- A set of grips `Γ` (e.g., the 6 faces {R, U, F, L, D, B} of a cube)
- A **grip group** `G` acting on `Γ` (e.g., rotational symmetries of the cube)

A **piece** is a subset of grips. Its key properties are:
- Solved grips `X ⊆ Γ` — which grips it was incident with when solved
- Attitude `g ∈ G` — the rotation from solved to current state
- Active grips `Y = g • X` — which grips it is currently incident with

A **twist** is specified by an axis (a grip `f`) and a rotation `r ∈ Stab(f)`.
-/

import Mathlib

universe u v

open MulAction Set Pointwise

variable {Γ : Type u} {G : Type v} [Group G] [MulAction G Γ]

/-! ## Pieces

A piece is identified by its set of solved grips `X ⊆ Γ`.
The grip group acts on `Set Γ` via the pointwise action (opened via `Pointwise`).
-/

/-- The set of active grips of a piece with solved grips `X` and attitude `g`. -/
def activeGrips (X : Set Γ) (g : G) : Set Γ :=
  g • X

/-
The solved grips can be recovered from active grips and attitude.
-/
theorem solvedGrips_eq (X : Set Γ) (g : G) :
    g⁻¹ • (activeGrips X g) = X := by
  unfold activeGrips;
  simp +decide [ Set.ext_iff, Set.mem_smul_set ]

/-
Active grips round-trip: recovering solved grips and recomputing active grips
    gives back the same active grips.
-/
theorem activeGrips_inv (X : Set Γ) (g : G) :
    activeGrips (g⁻¹ • activeGrips X g) g = activeGrips X g := by
  unfold activeGrips;
  simp +decide

/-! ## Piece Types

A piece type is an orbit of the action of `G` on `Set Γ`.
Two pieces are of the same type iff one can be rotated into the other.
-/

/-- Two pieces are of the same type if they are in the same orbit under `G`. -/
def samePieceType (G : Type v) [Group G] [MulAction G Γ] (X Y : Set Γ) : Prop :=
  X ∈ MulAction.orbit G Y

theorem samePieceType_refl (X : Set Γ) : samePieceType G X X := by
  exact ⟨ 1, by simp +decide ⟩

theorem samePieceType_symm {X Y : Set Γ} (h : samePieceType G X Y) :
    samePieceType G Y X := by
  obtain ⟨ g, rfl ⟩ := h;
  exact ⟨ g⁻¹, by simp +decide ⟩

theorem samePieceType_trans {X Y Z : Set Γ}
    (h₁ : samePieceType G X Y) (h₂ : samePieceType G Y Z) :
    samePieceType G X Z := by
  obtain ⟨ g, hg ⟩ := h₁;
  obtain ⟨ h, hh ⟩ := h₂;
  use g * h;
  grind +suggestions

/-- `samePieceType` is an equivalence relation. -/
theorem samePieceType_equivalence :
    Equivalence (samePieceType (Γ := Γ) G) :=
  ⟨samePieceType_refl, fun h => samePieceType_symm h, fun h₁ h₂ => samePieceType_trans h₁ h₂⟩

/-! ## Stabilizers and Piece Orientations

For a piece with active grips `Y`, its **orientation group** is the stabilizer
`Stab_G(Y)`, the set of `g ∈ G` such that `g • Y = Y`.
-/

/-- The stabilizer of a piece's grip set determines its orientation group. -/
def pieceOrientationGroup (Y : Set Γ) : Subgroup G :=
  MulAction.stabilizer G Y

/-! ## Twists

A twist is specified by:
- An axis `f : Γ` (a grip)
- A rotation `r ∈ Stab_G(f)` (an element of the stabilizer of `f`)

A twist acts on a piece: if the piece is currently incident with `f`
(i.e., `f ∈ Y`), the piece gets rotated by `r`; otherwise it stays put.
-/

/-- A twist on a grip system, consisting of an axis and a rotation fixing that axis. -/
structure Twist (Γ : Type u) (G : Type v) [Group G] [MulAction G Γ] where
  /-- The axis of the twist (the grip being turned). -/
  axis : Γ
  /-- The rotation, which must fix the axis. -/
  rotation : G
  /-- The rotation fixes the axis. -/
  axis_fixed : rotation • axis = axis

/-- Apply a twist to a piece given whether it's incident with the axis.
    If incident, compose attitude with the twist rotation; otherwise leave unchanged. -/
def Twist.applyToPiece (t : Twist Γ G) (incident : Bool) (attitude : G) : G :=
  if incident then attitude * t.rotation else attitude

/-
Applying a twist to a solved incident piece gives the twist rotation.
-/
theorem Twist.apply_solved_incident (t : Twist Γ G) :
    t.applyToPiece true 1 = t.rotation := by
  unfold Twist.applyToPiece
  simp [t.axis_fixed]

/-
Applying a twist to a non-incident piece leaves it unchanged.
-/
theorem Twist.apply_not_incident (t : Twist Γ G) (g : G) :
    t.applyToPiece false g = g := by
  simp [Twist.applyToPiece]

/-
Composing two twists on incident pieces gives the product of rotations.
-/
theorem Twist.apply_twice_incident (t₁ t₂ : Twist Γ G) (g : G) :
    t₂.applyToPiece true (t₁.applyToPiece true g) = g * t₁.rotation * t₂.rotation := by
  simp [Twist.applyToPiece, mul_assoc]

/-! ## Anti-Automorphism

The anti-automorphism maps a piece with active grip set `A` to the piece
whose active grip set is `Aᶜ` (the complement).
-/

/-- The anti-automorphism sends a piece to its complement. -/
def antiAutomorphism (X : Set Γ) : Set Γ := Xᶜ

/-
The anti-automorphism is an involution.
-/
theorem antiAutomorphism_involutive :
    Function.Involutive (antiAutomorphism (Γ := Γ)) := by
  exact fun x => compl_compl x

/-- The anti-automorphism is injective. -/
theorem antiAutomorphism_injective :
    Function.Injective (antiAutomorphism (Γ := Γ)) :=
  antiAutomorphism_involutive.injective

/-- The anti-automorphism is surjective. -/
theorem antiAutomorphism_surjective :
    Function.Surjective (antiAutomorphism (Γ := Γ)) :=
  antiAutomorphism_involutive.surjective

/-- The anti-automorphism is a bijection. -/
theorem antiAutomorphism_bijective :
    Function.Bijective (antiAutomorphism (Γ := Γ)) :=
  ⟨antiAutomorphism_injective, antiAutomorphism_surjective⟩

/-
The anti-automorphism commutes with the group action on sets.
-/
theorem antiAutomorphism_smul_comm (g : G) (X : Set Γ) :
    antiAutomorphism (g • X) = g • antiAutomorphism X := by
  convert Set.ext _;
  simp +decide [ antiAutomorphism, Set.mem_smul_set_iff_inv_smul_mem ]

/-
Anti-pieces of the same type are of the same type.
-/
theorem samePieceType_anti {X Y : Set Γ}
    (h : samePieceType G X Y) :
    samePieceType G (antiAutomorphism X) (antiAutomorphism Y) := by
  obtain ⟨g, hg⟩ : ∃ g : G, X = g • Y := by
    exact h.imp fun g hg => hg.symm;
  use g;
  simp +decide [ hg, antiAutomorphism_smul_comm ]