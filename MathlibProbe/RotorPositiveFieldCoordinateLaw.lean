import MathlibProbe.RotorPositiveFieldMomentLaw
import MathlibProbe.HeisenbergCoordinateMomentBounds
import Mathlib.Data.Finsupp.Multiset

/-!
# Local coordinate moments determine the Heisenberg free Gibbs limit

Each finitely supported lattice spin monomial gives a fixed list of individual
coordinates including their multiplicities. Once the cube contains its sites,
the ratio of physical finite integrals is exactly the correlation of that list
in every complex field. This connects finite-graph bounds for marked integrals
to convergence and stationarity of the full free-box probability laws.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace IsingScaling.Rotor.HeisenbergField.PositiveFieldLaw
open ComplexPartition PressureSelection PositiveFieldContinuation

/-- Expand the finitely supported exponents into repeated physical coordinates. -/
def latticeMarks (d : MomentDegree) : List (Site × Fin 3) := d.toMultiset.toList

theorem latticeMarks_eval (d : MomentDegree) (s : SpinField 3) :
    ((latticeMarks d).map (fun i => (s i.1).val i.2)).prod = spinMoment d s := by
  rw [latticeMarks,Multiset.prod_map_toList,Finsupp.toMultiset_map,Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index pow_zero pow_add,spinMoment_apply]
  rfl

/-- Coordinate ports used in the finite graph. Each lattice site eventually
belongs to the cube, so the default value of cubePort eventually plays no role. -/
def cubeMarks (n : ℕ) (d : MomentDegree) : List (BoxSite n × Fin 3) :=
  (latticeMarks d).map (fun i => (cubePort n i.1,i.2))

@[simp] theorem cubeMarks_length (n : ℕ) (d : MomentDegree) :
    (cubeMarks n d).length = (latticeMarks d).length := by simp [cubeMarks]

private theorem marks_inside (l : List (Site × Fin 3)) :
    ∀ᶠ n in atTop, ∀ i ∈ l, i.1 ∈ cube n := by
  induction l with
  | nil => simp
  | cons i l ih =>
    filter_upwards [BondMirror.ev_cube i.1,ih] with n hn hl
    simpa using And.intro hn hl

/-- Eventual equality holds simultaneously in the whole complex plane.
The readout observes spins at the prescribed sites before sending volume to infinity. -/
theorem coordinateRatio_eventually (β : ℝ) (d : MomentDegree) :
    ∀ᶠ n in atTop, ∀ z : ℂ,
      CoordinateMoments.ratio (cubeCoupling n β) (uniform z) (cubeMarks n d) =
      cubeRatio β (spinMoment d) n z := by
  filter_upwards [marks_inside (latticeMarks d)] with n hn
  have eqMark : CoordinateMoments.coordinateProduct (cubeMarks n d) =
      (spinMoment d).comp (extendCube n) := by
    ext s
    rw [CoordinateMoments.coordinateProduct_apply,ContinuousMap.comp_apply,
      ← latticeMarks_eval d (extendCube n s),cubeMarks,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp [extendCube,cubePort,hn i hi]
  intro z
  simp only [CoordinateMoments.ratio,cubeRatio,eqMark]

/-- A uniform complex estimate on actual finite coordinate lists, with a
different constant for each order and compact set, supplies all moment bounds
needed for convergence of probability laws. -/
theorem cubeMomentBounds_of_lists {β : ℝ}
    (hb : ∀ k : ℕ, ∀ K : Set ℂ, IsCompact K → K ⊆ rightHalfPlane →
      ∃ M : ℝ, ∀ n (marks : List (BoxSite n × Fin 3)), marks.length ≤ k →
        ∀ z ∈ K, ‖CoordinateMoments.ratio (cubeCoupling n β) (uniform z) marks‖ ≤ M) :
    CubeMomentBounds β := by
  intro d K hK hpos
  obtain ⟨M,hM⟩ := hb (latticeMarks d).length K hK hpos
  refine ⟨M,?_⟩
  filter_upwards [coordinateRatio_eventually β d] with n hn z hz
  rw [← hn z]
  exact hM n _ (by simp) z hz

/-- Each prescribed cube satisfies the finite-graph Lee–Yang theorem.
Bounds on its actual coordinate moments then hold uniformly as it grows. -/
theorem cubeMomentBounds_of_finiteLeeYang {β : ℝ}
    (hcube : ∀ n, FiniteLeeYangRotation.FiniteLeeYang (cubeCoupling n β)) :
    CubeMomentBounds β := by
  apply cubeMomentBounds_of_lists
  intro k K hK hpos
  obtain ⟨M,_,hm⟩ := CoordinateMoments.compact_coordinate_moments k hK (fun z hz => hpos hz)
  exact ⟨M,fun n l hl z hz => hm (cubeCoupling n β) (hcube n) z hz l hl⟩

/-- A finite-graph zero-free theorem in its single physical basis on the
cubes and rectangles gives the positive real field limit of the full spin law. -/
theorem positiveFieldThermodynamicInput_of_finiteLeeYang {β : ℝ} (hβ : 0 ≤ β)
    (hcube : ∀ n, FiniteLeeYangRotation.FiniteLeeYang (cubeCoupling n β))
    (hrect : ∀ n, FiniteLeeYangRotation.FiniteLeeYang (rectangleCoupling n β)) :
    PositiveFieldThermodynamicInput β :=
  positiveFieldThermodynamicInput_of_compact_moment_bounds hβ
    (FiniteLeeYangRotation.freeDotControl_of_finiteLeeYang _ _ hcube)
    (FiniteLeeYangRotation.freeDotControl_of_finiteLeeYang _ _ hrect)
    (cubeMomentBounds_of_finiteLeeYang hcube)

/-- For every positive field there is a unique stationary common free limit
and it satisfies the physical DLR equations at that same field. -/
theorem existsUnique_gibbs_common_free_limit_of_finiteLeeYang {β : ℝ} (hβ : 0 ≤ β)
    (hcube : ∀ n, FiniteLeeYangRotation.FiniteLeeYang (cubeCoupling n β))
    (hrect : ∀ n, FiniteLeeYangRotation.FiniteLeeYang (rectangleCoupling n β))
    {h : ℝ} (hh : 0 < h) :
    ∃! P : ProbabilityMeasure (SpinField 3), IsFieldGibbs β h P ∧ CommonFreeLimit β h P :=
  existsUnique_gibbs_common_free_limit hβ
    (FiniteLeeYangRotation.freeDotControl_of_finiteLeeYang _ _ hcube)
    (FiniteLeeYangRotation.freeDotControl_of_finiteLeeYang _ _ hrect)
    (cubeMomentBounds_of_finiteLeeYang hcube) hh

end IsingScaling.Rotor.HeisenbergField.PositiveFieldLaw
