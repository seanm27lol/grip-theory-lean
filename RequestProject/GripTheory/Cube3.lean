/-
# Grip Theory — The 3×3×3 Rubik's Cube

The 3×3×3 Rubik's cube has:
- 6 grips: `{R, U, F, L, D, B}`
- Grip group: the rotation group of the cube, isomorphic to `S₄` (order 24)

Piece types (orbits under the grip group action on subsets):
- Core: 1 piece with 0 grips, stabilizer = G (order 24)
- Centers: 6 pieces with 1 grip, stabilizer ≅ ℤ₄
- Edges: 12 pieces with 2 grips, stabilizer ≅ ℤ₂
- Corners: 8 pieces with 3 grips, stabilizer ≅ ℤ₃

The full state space is:
  `(ℤ₂ ≀ S₁₂) × (ℤ₃ ≀ S₈) × (ℤ₄ ≀ S₆) × (G ≀ S₁)`

Reference: https://hypercubing.xyz/theory/grip-theory/
-/

import Mathlib

/-! ## Face enumeration

We define the 6 faces of a cube.
-/

/-- The six faces of a cube. -/
inductive CubeFace : Type
  | R | U | F | L | D | B
  deriving DecidableEq, Fintype, Repr

namespace CubeFace

/-- The opposite face map. -/
def opposite : CubeFace → CubeFace
  | R => L
  | U => D
  | F => B
  | L => R
  | D => U
  | B => F

/-
Opposite is an involution.
-/
theorem opposite_involutive : Function.Involutive opposite := by
  exact fun x => by cases x <;> rfl;

/-
No face is its own opposite.
-/
theorem opposite_ne_self (f : CubeFace) : opposite f ≠ f := by
  decide +revert

/-
There are exactly 6 faces.
-/
theorem card_cubeFace : Fintype.card CubeFace = 6 := by
  rfl

end CubeFace

/-! ## Piece classification

We classify the subsets of `CubeFace` by cardinality, corresponding to
the different piece types of the 3×3×3.
-/

/-- A piece of the 3×3×3 is a `Finset CubeFace`. -/
abbrev CubePiece := Finset CubeFace

/-- A core piece has 0 grips. -/
def CubePiece.isCore (p : CubePiece) : Prop := p.card = 0

/-- A center piece has exactly 1 grip. -/
def CubePiece.isCenter (p : CubePiece) : Prop := p.card = 1

/-- An edge piece has exactly 2 adjacent grips. -/
def CubePiece.isEdge (p : CubePiece) : Prop :=
  p.card = 2 ∧ ∀ f₁ ∈ p, ∀ f₂ ∈ p, f₁ ≠ f₂ → f₂ ≠ CubeFace.opposite f₁

/-- A corner piece has exactly 3 mutually adjacent grips. -/
def CubePiece.isCorner (p : CubePiece) : Prop :=
  p.card = 3 ∧ ∀ f₁ ∈ p, ∀ f₂ ∈ p, f₁ ≠ f₂ → f₂ ≠ CubeFace.opposite f₁

/-
There are exactly 6 center pieces (one per face).
-/
theorem num_centers :
    (Finset.univ.filter (fun p : Finset CubeFace => p.card = 1)).card = 6 := by
  native_decide

/-
There are exactly 12 edge pieces (pairs of adjacent faces).
-/
theorem num_edges :
    (Finset.univ.filter (fun p : Finset CubeFace =>
      p.card = 2 ∧ ∀ f₁ ∈ p, ∀ f₂ ∈ p, f₁ ≠ f₂ →
        f₂ ≠ CubeFace.opposite f₁)).card = 12 := by
  decide +revert

/-
There are exactly 8 corner pieces (triples of mutually adjacent faces).
-/
theorem num_corners :
    (Finset.univ.filter (fun p : Finset CubeFace =>
      p.card = 3 ∧ ∀ f₁ ∈ p, ∀ f₂ ∈ p, f₁ ≠ f₂ →
        f₂ ≠ CubeFace.opposite f₁)).card = 8 := by
  decide +revert

/-! ## Complex 3×3×3

The complex 3×3×3 includes all 2^6 = 64 possible subsets of grips as pieces.
-/

/-
The complex 3×3×3 has 64 pieces.
-/
theorem complex_cube_num_pieces :
    Fintype.card (Finset CubeFace) = 64 := by
  decide +revert