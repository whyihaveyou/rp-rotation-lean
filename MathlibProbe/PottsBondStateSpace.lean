import MathlibProbe.CubicIsingTwoPoint
import Mathlib.Data.Sym.Sym2

/-! Nearest-neighbour, unoriented bonds of the cubic lattice and the
events that the open bonds join two sites inside a cube or on the lattice. -/

noncomputable section
open scoped Classical
namespace IsingScaling.Potts.FreeBond

def IsBond (e : Sym2 Site) : Prop :=
  ∃ x y : Site, e = s(x, y) ∧ latticeDistance x y = 1

abbrev Bond := {e : Sym2 Site // IsBond e}
abbrev Field := Bond → Bool

def window (L : ℕ) : Finset Bond :=
  (((cube L).product (cube L)).image (fun e => s(e.1, e.2))).subtype IsBond

/-- Reflexive, symmetric and transitive closure is existence of a finite
open path. At each step the unordered bond must belong to this window. -/
def within (L : ℕ) (x y : Site) : Set Field :=
  {ω | Relation.EqvGen
    (fun u v : Site => ∃ e ∈ window L, e.val = s(u, v) ∧ ω e = true) x y}

def connection (x y : Site) : Set Field :=
  {ω | Relation.EqvGen (fun u v : Site => ∃ e : Bond, e.val = s(u, v) ∧ ω e = true) x y}

end IsingScaling.Potts.FreeBond
