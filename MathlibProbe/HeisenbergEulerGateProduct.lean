import MathlibProbe.HeisenbergSpinorPhysicalGates
import MathlibProbe.HeisenbergClassicalEulerLimit
import MathlibProbe.HeisenbergAsanoWire
import MathlibProbe.HeisenbergEulerTensorIntegral
import MathlibProbe.HeisenbergSiteSymmetrization

/-! # Independent ports of the classical finite-volume Euler approximant

Every repetition of a directed bond (x,y) receives two distinct ports, even
if x=y. The field at x receives one port per repetition. Each port carries
a separate row and column variable. Splitting a binary assignment into its
restrictions to the gate occurrences factors the finite sum over all row and
column assignments. Thus the full boundary polynomial is a product of the
physical one- and two-port gate polynomials. Their open-polydisk estimates
apply uniformly over a compact set of admissible complex fields.

This convention indexes all directed coupling entries Jxy. The exchange
matrix has coefficient Jxy/n and therefore contributes
1+Jxy(1+Sx·Sy)/(2n) to the scalar Euler weight.
-/
noncomputable section
open Finset Filter MeasureTheory
open scoped Classical Topology InnerProductSpace
namespace IsingScaling.Rotor.HeisenbergField.EulerGates
open ClassicalEuler ComplexPartition SpinorGates

abbrev Occ (V : Type*) (n : ℕ) := Fin n × Labels V

/-- False and true are the first and second endpoints of an ordered bond. -/
def PortOf {V : Type*} : Labels V → Type
  | .inl _ => Bool
  | .inr _ => Unit

instance {V : Type*} : (l : Labels V) → Fintype (PortOf l)
  | .inl _ => inferInstanceAs (Fintype Bool)
  | .inr _ => inferInstanceAs (Fintype Unit)

instance {V : Type*} : (l : Labels V) → DecidableEq (PortOf l)
  | .inl _ => inferInstanceAs (DecidableEq Bool)
  | .inr _ => inferInstanceAs (DecidableEq Unit)

abbrev Port (V : Type*) (n : ℕ) := Σ o : Occ V n, PortOf o.2

def siteOf {V : Type*} : (l : Labels V) → PortOf l → V
  | .inl (x,y), b => if (show Bool from b) = true then y else x
  | .inr x, _ => x

def loc {V : Type*} {n : ℕ} (p : Port V n) : V := siteOf p.1.2 p.2

abbrev Bits := Bool × Bool
variable {V : Type*}

def localMatrix (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) :
    (l : Labels V) → Matrix (PortOf l → Bool) (PortOf l → Bool) ℂ
  | .inl (x,y), r,c => exchangeEntry (J x y / (n:ℝ)) (r false,r true) (c false,c true)
  | .inr x, r,c => fieldEntry (1/(n:ℝ)) (H x) (r ()) (c ())

variable [Fintype V]

/-- The tensor product of all actual ordered-bond and site-field Euler matrices. -/
def productMatrix (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) :
    Matrix (Port V n → Bool) (Port V n → Bool) ℂ :=
  fun r c => ∏ o : Occ V n, localMatrix J H n o.2
    (fun p => r ⟨o,p⟩) (fun p => c ⟨o,p⟩)

/-- Independent binary row and column assignments for every gate port. -/
def openSymbol (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) (v : Port V n → ℂ × ℂ) : ℂ :=
  ∑ ξ : Port V n → Bits,
    productMatrix J H n (fun p => (ξ p).1) (fun p => (ξ p).2) *
    ∏ p, (leg (v p).1 (ξ p).1 * leg (v p).2 (ξ p).2)

def localSymbol (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) :
    (l : Labels V) → (PortOf l → ℂ × ℂ) → ℂ
  | .inl (x,y), v => twoLegSymbol (exchangeEntry (J x y/(n:ℝ)))
      (v false).1 (v true).1 (v false).2 (v true).2
  | .inr x, v => oneLegSymbol (fieldEntry (1/(n:ℝ)) (H x)) (v ()).1 (v ()).2

omit [Fintype V] in
private theorem localSymbol_sum (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ)
    (l : Labels V) (v : PortOf l → ℂ × ℂ) :
    (∑ ξ : PortOf l → Bits, localMatrix J H n l (fun p => (ξ p).1) (fun p => (ξ p).2) *
      ∏ i, (leg (v i).1 (ξ i).1 * leg (v i).2 (ξ i).2)) = localSymbol J H n l v := by
  cases l with
  | inl edge =>
    rcases edge with ⟨x,y⟩
    let f (q : Bool → Bits) := exchangeEntry (J x y/(n:ℝ))
      ((q false).1,(q true).1) ((q false).2,(q true).2) *
      ∏ i : Bool, leg (v i).1 (q i).1 * leg (v i).2 (q i).2
    change (∑ q, f q) = _
    rw [← (Equiv.boolArrowEquivProd Bits).symm.sum_comp f]
    simp [f,localSymbol,twoLegSymbol,Fintype.sum_prod_type,
      Equiv.boolArrowEquivProd,leg]
    ring
  | inr x =>
    let f (q : Unit → Bits) := fieldEntry (1/(n:ℝ)) (H x) (q ()).1 (q ()).2 *
      (leg (v ()).1 (q ()).1 * leg (v ()).2 (q ()).2)
    change (∑ q : Unit → Bits, localMatrix J H n (Sum.inr x) (fun p => (q p).1)
      (fun p => (q p).2) * ∏ i : Unit, (leg (v i).1 (q i).1 * leg (v i).2 (q i).2)) = _
    simp only [Fintype.prod_unique]
    change (∑ q, f q) = _
    rw [← (Equiv.funUnique Unit Bits).symm.sum_comp f]
    simp [f,localSymbol,oneLegSymbol,Fintype.sum_prod_type,Equiv.funUnique,mul_assoc]

/-- Exact polynomial identity on all independent complex port variables. -/
theorem openSymbol_eq_product (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) (v : Port V n → ℂ × ℂ) :
    openSymbol J H n v = ∏ o : Occ V n, localSymbol J H n o.2 (fun p => v ⟨o,p⟩) := by
  let F (o : Occ V n) (q : PortOf o.2 → Bits) := localMatrix J H n o.2
    (fun p => (q p).1) (fun p => (q p).2) *
    ∏ p, (leg (v ⟨o,p⟩).1 (q p).1 * leg (v ⟨o,p⟩).2 (q p).2)
  calc
    openSymbol J H n v = ∑ ξ : Port V n → Bits,
        ∏ o : Occ V n, F o (fun p => ξ ⟨o,p⟩) := by
      unfold openSymbol
      apply Finset.sum_congr rfl
      intro ξ _
      unfold productMatrix
      rw [Fintype.prod_sigma, ← Finset.prod_mul_distrib]
    _ = ∑ q : (o : Occ V n) → PortOf o.2 → Bits, ∏ o, F o (q o) :=
      (Equiv.piCurry fun (o : Occ V n) (_ : PortOf o.2) => Bits).sum_comp
        (fun q => ∏ o, F o (q o))
    _ = ∏ o : Occ V n, ∑ q, F o q := (Fintype.prod_sum F).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro o _
      exact localSymbol_sum J H n o.2 (fun p => v ⟨o,p⟩)

/-- Pointwise disk stability as soon as all the actual one-site gates are stable. -/
theorem openSymbol_nonzero_of_field_gates (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y)
    (H : ComplexPartition.Field V) (n : ℕ)
    (gates : ∀ x, ∀ a b : ℂ, ‖a‖<1 → ‖b‖<1 →
      oneLegSymbol (fieldEntry (1/(n:ℝ)) (H x)) a b ≠ 0)
    (v : Port V n → ℂ × ℂ) (hv : ∀ p, ‖(v p).1‖<1 ∧ ‖(v p).2‖<1) :
    openSymbol J H n v ≠ 0 := by
  rw [openSymbol_eq_product]
  apply Finset.prod_ne_zero_iff.mpr
  rintro ⟨i, e | x⟩ _
  · rcases e with ⟨x,y⟩
    exact exchange_disk_nonzero (div_nonneg (hJ x y) (Nat.cast_nonneg _))
      (hv ⟨(i,.inl (x,y)), false⟩).1 (hv ⟨(i,.inl (x,y)), true⟩).1
      (hv ⟨(i,.inl (x,y)), false⟩).2 (hv ⟨(i,.inl (x,y)), true⟩).2
  · exact gates x _ _ (hv ⟨(i,.inr x), ()⟩).1 (hv ⟨(i,.inr x), ()⟩).2

/-- One Euler index threshold for all independent port variables over every
field in the compact set. There is no uniformity assumption on the couplings. -/
theorem openSymbol_eventually_nonzero {T : Type*} [TopologicalSpace T] {K : Set T}
    (hK : IsCompact K) (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y)
    (H : T → ComplexPartition.Field V) (hc : ∀ x j, ContinuousOn (fun z => H z x j) K)
    (hcone : ∀ z ∈ K, ∀ x, ‖H z x 1‖+‖H z x 2‖ < (H z x 0).re) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ K, ∀ v : Port V n → ℂ × ℂ,
      (∀ p, ‖(v p).1‖<1 ∧ ‖(v p).2‖<1) → openSymbol J (H z) n v ≠ 0 := by
  filter_upwards [field_gates_eventually_on_compact hK H hc hcone] with n hn
  intro z hz v hv
  exact openSymbol_nonzero_of_field_gates J hJ _ n (fun x => hn x z hz) v hv

/-- Any enumeration of physical ports gives precisely the row and column
table expected by the Asano wire contraction. -/
def indexedCoefficient (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) {d : ℕ}
    (e : Port V n ≃ Fin d) (ξ : Fin d → Bits) : ℂ :=
  productMatrix J H n (fun p => (ξ (e p)).1) (fun p => (ξ (e p)).2)

theorem denseSymbol_eq_openSymbol (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) {d : ℕ}
    (e : Port V n ≃ Fin d) (v : Fin d → ℂ × ℂ) :
    MathlibProbe.HeisenbergAsanoWire.denseSymbol d (indexedCoefficient J H n e) v =
      openSymbol J H n (fun p => v (e p)) := by
  let E : (Port V n → Bits) ≃ (Fin d → Bits) := e.arrowCongr (Equiv.refl Bits)
  let f (ξ : Fin d → Bits) := indexedCoefficient J H n e ξ *
    ∏ i, (leg (v i).1 (ξ i).1 * leg (v i).2 (ξ i).2)
  change (∑ ξ, f ξ) = _
  rw [← E.sum_comp f]
  unfold openSymbol
  apply Finset.sum_congr rfl
  intro ξ _
  change indexedCoefficient J H n e (E ξ) *
    (∏ i, (leg (v i).1 ((E ξ) i).1 * leg (v i).2 ((E ξ) i).2)) = _
  have pull (j : Fin d) : E ξ j = ξ (e.symm j) := rfl
  simp only [indexedCoefficient, pull, Equiv.symm_apply_apply]
  congr 1
  simpa using (e.prod_comp (fun j => leg (v j).1 (ξ (e.symm j)).1 *
    leg (v j).2 (ξ (e.symm j)).2)).symm

/-- The stability hypothesis at the exact input type of the wire theorem. -/
theorem denseSymbol_eventually_nonzero {T : Type*} [TopologicalSpace T] {K : Set T}
    (hK : IsCompact K) (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y)
    (H : T → ComplexPartition.Field V) (hc : ∀ x j, ContinuousOn (fun z => H z x j) K)
    (hcone : ∀ z ∈ K, ∀ x, ‖H z x 1‖+‖H z x 2‖ < (H z x 0).re) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ K, ∀ {d : ℕ} (e : Port V n ≃ Fin d) (v : Fin d → ℂ × ℂ),
      (∀ i, ‖(v i).1‖<1 ∧ ‖(v i).2‖<1) →
      MathlibProbe.HeisenbergAsanoWire.denseSymbol d (indexedCoefficient J (H z) n e) v ≠ 0 := by
  filter_upwards [openSymbol_eventually_nonzero hK J hJ H hc hcone] with n h
  intro z hz d e v hv
  rw [denseSymbol_eq_openSymbol]
  exact h z hz _ (fun p => hv (e p))

/-- The input expected directly by the site symmetrizer, with its Fin-to-port enumeration. -/
theorem stable_of_field_gates (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y)
    (H : ComplexPartition.Field V) (n : ℕ)
    (gates : ∀ x, ∀ a b : ℂ, ‖a‖<1 → ‖b‖<1 →
      oneLegSymbol (fieldEntry (1/(n:ℝ)) (H x)) a b ≠ 0)
    {d : ℕ} (e : Fin d ≃ Port V n) :
    SiteSymmetrization.Stable e (productMatrix J H n) := by
  intro v hv
  change MathlibProbe.HeisenbergAsanoWire.denseSymbol d
    (indexedCoefficient J H n e.symm) v ≠ 0
  rw [denseSymbol_eq_openSymbol]
  exact openSymbol_nonzero_of_field_gates J hJ H n gates _ (fun p => hv (e.symm p))

/-- Each physical gate-matrix coefficient is an entire function of every affine field path. -/
theorem differentiable_productMatrix_affine (J : V → V → ℝ)
    (H D : ComplexPartition.Field V) (n : ℕ) (r c : Port V n → Bool) :
    Differentiable ℂ (fun z => productMatrix J (ComplexPartition.affine H D z) n r c) := by
  unfold productMatrix
  apply Differentiable.fun_finsetProd
  rintro ⟨i, e | x⟩ _
  · rcases e with ⟨x,y⟩
    exact differentiable_const _
  · have individual (u b : Bool) : Differentiable ℂ (fun z =>
        fieldEntry (1/(n:ℝ)) (ComplexPartition.affine H D z x) u b) := by
      cases u <;> cases b <;> simp only [fieldEntry,ComplexPartition.affine] <;> fun_prop
    exact individual (r ⟨(i,.inr x),()⟩) (c ⟨(i,.inr x),()⟩)

private theorem sum_bool_word (f : (Bool → Bool) → ℂ) :
    (∑ q, f q) = ∑ a : Bool, ∑ b : Bool, f (fun i => if i then b else a) := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp f]
  simp [Equiv.boolArrowEquivProd,Fintype.sum_prod_type]

private theorem sum_unit_word (f : (Unit → Bool) → ℂ) :
    (∑ q, f q) = ∑ a : Bool, f (fun _ => a) :=
  ((Equiv.funUnique Unit Bool).symm.sum_comp f).symm

private theorem univ_instances_eq {T : Type*} (D E : Fintype T) :
    @Finset.univ T D = @Finset.univ T E :=
  congrArg (fun F => @Finset.univ T F) (Subsingleton.elim D E)

omit [Fintype V] in
/-- A directed bond and a site field give their actual classical scalar factors. -/
theorem local_evaluation (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ)
    (l : Labels V) (s : Config V) :
    EulerTensor.evaluation (siteOf l) (localMatrix J H n l) s =
      1 + coefficient J H l s/(n:ℂ) := by
  cases l with
  | inl edge =>
    rcases edge with ⟨x,y⟩
    calc
      _ = (∑ r : Bool → Bool, ∑ c : Bool → Bool,
          exchangeEntry (J x y/(n:ℝ)) (r false,r true) (c false,c true) *
            ∏ p : Bool, BlochSphere.entry (s (if p then y else x)) (c p) (r p)) := by
        unfold EulerTensor.evaluation
        apply Finset.sum_congr (univ_instances_eq _ _)
        intro r _
        apply Finset.sum_congr (univ_instances_eq _ _)
        intro c _
        rfl
      _ = twoLegTrace (BlochSphere.entry (s x)) (BlochSphere.entry (s y))
            (exchangeEntry (J x y/(n:ℝ))) := by
        simp only [sum_bool_word,twoLegTrace,Fintype.prod_bool,Bool.false_eq_true,
          ↓reduceIte, Fintype.sum_bool]
        ring
      _ = _ := by
        rw [physical_bond_gate]
        simp [coefficient]
        ring
  | inr x =>
    calc
      _ = (∑ r : Unit → Bool, ∑ c : Unit → Bool, fieldEntry (1/(n:ℝ)) (H x) (r ()) (c ()) *
          ∏ p : Unit, BlochSphere.entry (s x) (c p) (r p)) := by
        unfold EulerTensor.evaluation
        apply Finset.sum_congr (univ_instances_eq _ _)
        intro r _
        apply Finset.sum_congr (univ_instances_eq _ _)
        intro c _
        rfl
      _ = oneLegTrace (BlochSphere.entry (s x)) (fieldEntry (1/(n:ℝ)) (H x)) := by
        simp [sum_unit_word,oneLegTrace]
      _ = _ := by
        rw [physical_field_gate]
        simp [coefficient]
        ring

/-- Evaluating the independent-leg matrix against one common Bloch spin at
each physical vertex gives the prescribed classical Euler integrand. -/
theorem evaluation_euler (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) (s : Config V) :
    EulerTensor.evaluation (loc (V := V) (n := n)) (productMatrix J H n) s =
      eulerWeight J H n s := by
  change EulerTensor.evaluation loc (EulerTensor.gateTensor
    (fun o : Occ V n => localMatrix J H n o.2)) s = _
  rw [EulerTensor.product_evaluation]
  change (∏ o : Occ V n, EulerTensor.evaluation (siteOf o.2) (localMatrix J H n o.2) s) = _
  simp only [local_evaluation,Fintype.prod_prod_type]
  rw [Finset.prod_comm]
  simp [eulerWeight]

/-- Exact physical trace formula with the positive Bloch normalization. -/
theorem approximant_eq_trace (J : V → V → ℝ) (H : ComplexPartition.Field V) (n : ℕ) :
    approximant J H n =
      (EulerTensor.dimensionFactor (loc (V := V) (n := n)) : ℂ) *
        Matrix.trace (EulerTensor.siteSym loc * productMatrix J H n) := by
  calc
    approximant J H n = ∫ s : Config V,
        EulerTensor.evaluation (loc (V := V) (n := n)) (productMatrix J H n) s ∂surfaceProduct V := by
      unfold approximant
      apply integral_congr_ae
      exact Eventually.of_forall fun s => (evaluation_euler J H n s).symm
    _ = _ := by
      have h := EulerTensor.integral_evaluation (loc (V := V) (n := n)) (productMatrix J H n)
      rw [h]
      apply congrArg ((EulerTensor.dimensionFactor (loc (V := V) (n := n)) : ℂ) * ·)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      apply Finset.sum_congr (univ_instances_eq _ _)
      intro i _
      apply Finset.sum_congr (univ_instances_eq _ _)
      intro j _
      rfl

#print axioms openSymbol_eq_product
#print axioms denseSymbol_eventually_nonzero
#print axioms stable_of_field_gates
#print axioms differentiable_productMatrix_affine
#print axioms local_evaluation
#print axioms evaluation_euler
#print axioms approximant_eq_trace
end IsingScaling.Rotor.HeisenbergField.EulerGates
