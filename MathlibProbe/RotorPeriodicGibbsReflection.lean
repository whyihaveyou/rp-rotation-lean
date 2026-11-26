import MathlibProbe.RotorPrecisionPhysicalSplit
import MathlibProbe.RotorPeriodicFirstVariation
import MathlibProbe.RotorBondReflection

/-! # Reflection on a finite spherical Gibbs torus

Split the sites into the fixed wall and two reflected copies of its open
half. A symmetric invariant coupling gives one common half energy on each
copy, with half of the wall energy assigned to each side. The remaining
coupling K is the matrix from the positive sites to their reflections. If
K is positive semidefinite, factor it as B* B. The cross exponential is
then a product of exponential inner-product kernels of the transformed
spins. Integrating their finite Gram inequalities independently on the two
halves, with identical weights and signed tests, yields a nonnegative
quantity for each fixed wall assignment. Integrating over the wall and
normalizing gives reflection positivity for the actual finite Gibbs law.
-/

noncomputable section
open scoped Classical Topology InnerProductSpace MatrixOrder
open MeasureTheory Finset Matrix
namespace IsingScaling.Rotor.PressureSelection.PeriodicGibbsReflection
open PhysicalSplit

private abbrev Config (N : ℕ) (T : Type*) := T → Spin N
private abbrev Record (N : ℕ) {T : Type*} (H : Half T) :=
  Config N H.Wall × Config N H.Plus × Config N H.Plus
private abbrev WPP {T : Type*} (H : Half T) := H.Wall ⊕ (H.Plus ⊕ H.Plus)
private def perm (P W : Type*) : (W ⊕ (P ⊕ P)) ≃ PrecisionReflection.Sites P W where
  toFun
    | .inl w => .inr (.inr w)
    | .inr (.inl v) => .inl v
    | .inr (.inr v) => .inr (.inl v)
  invFun
    | .inl v => .inr (.inl v)
    | .inr (.inl v) => .inr (.inr v)
    | .inr (.inr w) => .inl w
  left_inv := by rintro (w | (v | v)) <;> rfl
  right_inv := by rintro (v | (v | w)) <;> rfl
private def label {T : Type*} (H : Half T) : WPP H ≃ T :=
  (perm H.Plus H.Wall).trans H.equiv

private def paste {N : ℕ} {T : Type*} (H : Half T) (k : Record N H) (x : T) : Spin N :=
  Sum.elim k.1 (Sum.elim k.2.1 k.2.2) ((label H).symm x)

private theorem paste_on {N : ℕ} {T : Type*} (H : Half T) (k : Record N H) (i : WPP H) :
    paste H k (label H i) = Sum.elim k.1 (Sum.elim k.2.1 k.2.2) i := by simp [paste]

private theorem paste_continuous {N : ℕ} {T : Type*} (H : Half T) :
    Continuous (paste (N:=N) H) := by
  apply continuous_pi
  intro x
  unfold paste
  cases (label H).symm x with
  | inl _ => simp only [Sum.elim_inl]; fun_prop
  | inr i => cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop

private abbrev prior (N : ℕ) (V : Type*) [Fintype V] :
    Measure (Config N V) := Measure.pi fun _ => SiteReflection.surfacePrior N

private theorem paste_preserving {N : ℕ} [NeZero N] {T : Type*} [Fintype T] (H : Half T) :
    MeasurePreserving (paste (N:=N) H)
      ((prior N H.Wall).prod ((prior N H.Plus).prod (prior N H.Plus))) (prior N T) := by
  let e := (label H).symm
  let θ := SiteReflection.surfacePrior N
  have h1 := measurePreserving_sumPiEquivProdPi_symm (fun _ : H.Plus ⊕ H.Plus => θ)
  have h2 := measurePreserving_sumPiEquivProdPi_symm (fun _ : WPP H => θ)
  have h3 := (measurePreserving_piCongrLeft (fun _ : WPP H => θ) e).symm
  have h := h3.comp (h2.comp ((MeasurePreserving.id (prior N H.Wall)).prod h1))
  convert h using 1
  funext k x
  change Sum.elim k.1 (Sum.elim k.2.1 k.2.2) (e x) =
    (Equiv.piCongrLeft (fun _ => Spin N) e).symm
      (Sum.elim k.1 (Sum.elim k.2.1 k.2.2)) x
  rw [Equiv.piCongrLeft_symm_apply]

private def block {N : ℕ} {T I J : Type*} [Fintype I] [Fintype J] (A : T → T → ℝ)
    (x : I → T) (y : J → T) (u : Config N I) (v : Config N J) : ℝ :=
  ∑ i, ∑ j, A (x i) (y j)*⟪(u i).val,(v j).val⟫_ℝ

private theorem block_swap {N : ℕ} {T I J : Type*} [Fintype I] [Fintype J] (A : T → T → ℝ)
    (h : ∀ x y, A x y=A y x) (x : I → T) (y : J → T) (u : Config N I) (v : Config N J) :
    block A x y u v = block A y x v u := by
  unfold block
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [h (x i) (y j),real_inner_comm (u i).val (v j).val]

private def pos {T : Type*} (H : Half T) (x : H.Plus) : T := x.val
private def neg {T : Type*} (H : Half T) (x : H.Plus) : T := H.refl x.val
private def wall {T : Type*} (H : Half T) (w : H.Wall) : T := w.val

private def halfEnergy {N : ℕ} {T : Type*} [Fintype T] (H : Half T) (A : T → T → ℝ)
    (b : Config N H.Wall) (u : Config N H.Plus) : ℝ :=
  block A (pos H) (pos H) u u / 2 + block A (pos H) (wall H) u b +
    block A (wall H) (wall H) b b / 4

private def crossEnergy {N : ℕ} {P : Type*} [Fintype P] (K : Matrix P P ℝ)
    (u v : Config N P) : ℝ := block K id id u v

/-- The matrix of interactions across the open halves, with the receiving
coordinates reflected back into the positive half. -/
def crossMatrix {T : Type*} (H : Half T) (A : T → T → ℝ) : Matrix H.Plus H.Plus ℝ :=
  Matrix.of fun x y => A x.val (H.refl y.val)

private theorem energy_split {N : ℕ} {T : Type*} [Fintype T] (H : Half T) (A : T → T → ℝ)
    (hs : ∀ x y, A x y=A y x) (hr : ∀ x y, A (H.refl x) (H.refl y)=A x y)
    (b : Config N H.Wall) (u v : Config N H.Plus) :
    energy A (paste H (b,u,v)) =
      halfEnergy H A b u + halfEnergy H A b v + crossEnergy (crossMatrix H A) u v := by
  let e := label H
  let s := paste H (b,u,v)
  have hf (j : H.Wall) : H.refl (wall H j) = wall H j := j.property
  have hnn : block A (neg H) (neg H) v v = block A (pos H) (pos H) v v := by
    simp only [block,neg,pos,hr]
  have hnw : block A (neg H) (wall H) v b = block A (pos H) (wall H) v b := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change A (H.refl i.val) (wall H j)*_ = A i.val (wall H j)*_
    rw [← hr i.val (wall H j),hf]
  have hcross : block A (pos H) (neg H) u v = crossEnergy (crossMatrix H A) u v := rfl
  have core : energy A s =
      (block A (wall H) (wall H) b b + block A (wall H) (pos H) b u +
       block A (wall H) (neg H) b v + block A (pos H) (wall H) u b +
       block A (pos H) (pos H) u u + block A (pos H) (neg H) u v +
       block A (neg H) (wall H) v b + block A (neg H) (pos H) v u +
       block A (neg H) (neg H) v v)/2 := by
    let q (x y : T) := A x y * ⟪(s x).val,(s y).val⟫_ℝ
    have he : energy A s = (∑ i : WPP H, ∑ j : WPP H, q (e i) (e j))/2 := by
      change (∑ x, ∑ y, q x y)/2 = _
      congr 1
      rw [← e.sum_comp (fun x => ∑ y, q x y)]
      exact Finset.sum_congr rfl fun i _ => (e.sum_comp (q (e i))).symm
    rw [he]
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, q,s,e,paste_on,
      Sum.elim_inl,Sum.elim_inr]
    change ((block A (wall H) (wall H) b b +
      (block A (pos H) (wall H) u b + block A (neg H) (wall H) v b)) +
      ((block A (wall H) (pos H) b u +
       (block A (pos H) (pos H) u u + block A (neg H) (pos H) v u)) +
       (block A (wall H) (neg H) b v +
       (block A (pos H) (neg H) u v + block A (neg H) (neg H) v v)))) / 2 = _
    ring
  rw [core,block_swap A hs (wall H) (pos H),block_swap A hs (wall H) (neg H),
    block_swap A hs (neg H) (pos H),hnw,hnn,hcross]
  unfold halfEnergy
  ring

private theorem exp_cross_samples {N : ℕ} {P I : Type*} [Fintype P] [Fintype I]
    (K : Matrix P P ℝ) (hK : K.PosSemidef) (s : I → Config N P) :
    (Matrix.of fun i j => Real.exp (crossEnergy K (s i) (s j))).PosSemidef := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.nonneg
  let a (i : I) (k : P) := ∑ x : P, B k x • (s i x).val
  have step (i j : I) : crossEnergy K (s i) (s j) = ∑ k : P, ⟪a i k,a j k⟫_ℝ := by
    simp only [crossEnergy,block,id_eq,hB,Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.conjTranspose_apply,star_trivial,Finset.sum_mul,
      a,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
    conv_lhs =>
      arg 2
      ext x
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have eq : (Matrix.of fun i j => Real.exp (crossEnergy K (s i) (s j))) =
      Matrix.of (fun i j => ∏ k : P, Real.exp ((1:ℝ)*⟪a i k,a j k⟫_ℝ)) := by
    ext i j
    simp only [Matrix.of_apply,step,Real.exp_sum,one_mul]
  rw [eq]
  exact seam_posSemidef Finset.univ (fun _ => 1) (fun _ _ => zero_le_one) a

private theorem paste_left {N : ℕ} {T : Type*} (H : Half T) (b : Config N H.Wall)
    (u v : Config N H.Plus) (x : T) (hx : H.closed x) :
    paste H (b,u,v) x = paste H (b,u,u) x := by
  rcases hx with hp | hw
  · let i : WPP H := .inr (.inl ⟨x,hp⟩)
    change paste H (b,u,v) (label H i) = paste H (b,u,u) (label H i)
    rw [paste_on,paste_on]
    rfl
  · let i : WPP H := .inl ⟨x,hw⟩
    change paste H (b,u,v) (label H i) = paste H (b,u,u) (label H i)
    rw [paste_on,paste_on]
    rfl

private theorem paste_right {N : ℕ} {T : Type*} (H : Half T) (b : Config N H.Wall)
    (u v : Config N H.Plus) (x : T) (hx : H.closed x) :
    paste H (b,u,v) (H.refl x) = paste H (b,v,v) x := by
  rcases hx with hp | hw
  · let i : WPP H := .inr (.inr ⟨x,hp⟩)
    let j : WPP H := .inr (.inl ⟨x,hp⟩)
    change paste H (b,u,v) (label H i) = paste H (b,v,v) (label H j)
    rw [paste_on,paste_on]
    rfl
  · rw [hw]
    let i : WPP H := .inl ⟨x,hw⟩
    change paste H (b,u,v) (label H i) = paste H (b,v,v) (label H i)
    rw [paste_on,paste_on]
    rfl

private theorem energy_cont {N : ℕ} {T : Type*} [Fintype T] (A : T → T → ℝ) :
    Continuous (energy (N:=N) A) := by
  unfold energy
  fun_prop

private theorem cross_cont {N : ℕ} {P : Type*} [Fintype P] (K : Matrix P P ℝ) :
    Continuous (fun q : Config N P × Config N P => crossEnergy K q.1 q.2) := by
  unfold crossEnergy block
  fun_prop

private theorem half_cont {N : ℕ} {T : Type*} [Fintype T] (H : Half T)
    (A : T → T → ℝ) (b : Config N H.Wall) : Continuous (halfEnergy H A b) := by
  unfold halfEnergy block
  fun_prop

private theorem cross_integral {N : ℕ} [NeZero N] {P : Type*} [Fintype P]
    (K : Matrix P P ℝ) (hK : K.PosSemidef) (f : Config N P → ℝ) (hf : Continuous f) :
    0 ≤ ∫ q : Config N P × Config N P, f q.1*f q.2*Real.exp (crossEnergy K q.1 q.2)
        ∂((prior N P).prod (prior N P)) := by
  let A (q : Config N P × Config N P) := f q.1*f q.2*Real.exp (crossEnergy K q.1 q.2)
  have hc : Continuous A := ((hf.comp continuous_fst).mul (hf.comp continuous_snd)).mul (cross_cont K).rexp
  apply integral_nonneg_of_sample_sum (prior N P) A
  · exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc.comp (continuous_id.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro k x
    have h := (exp_cross_samples K hK x).dotProduct_mulVec_nonneg (fun i => f (x i))
    simpa only [A,Matrix.mulVec,dotProduct,Pi.star_apply,star_trivial,Finset.mul_sum,
      Matrix.of_apply,← mul_assoc,mul_right_comm] using h

/-- The actual normalized surface-spin Gibbs law is reflection positive
on continuous tests supported in the *closed* half, including the wall. -/
theorem sphereGibbs_reflected_test (N : ℕ) [NeZero N] {T : Type*} [Fintype T]
    (H : Half T) (A : T → T → ℝ) (hs : ∀ x y, A x y=A y x)
    (hr : ∀ x y, A (H.refl x) (H.refl y)=A x y) (hK : (crossMatrix H A).PosSemidef)
    (F : C(T → Spin N, ℝ))
    (half : ∀ s t : T → Spin N, (∀ x, H.closed x → s x=t x) → F s=F t) :
    0 ≤ ∫ s, F s * F (s ∘ H.refl) ∂(sphereGibbs N A : Measure _) := by
  let G (s : T → Spin N) := Real.exp (energy A s) * (F s * F (s ∘ H.refl))
  have hG : Continuous G := (energy_cont A).rexp.mul (F.continuous.mul (F.continuous.comp
    (continuous_pi fun x => continuous_apply (H.refl x))))
  let q (b : Config N H.Wall) (u : Config N H.Plus) :=
    Real.exp (halfEnergy H A b u)*F (paste H (b,u,u))
  have hq (b : Config N H.Wall) : Continuous (q b) := (half_cont H A b).rexp.mul
    (F.continuous.comp ((paste_continuous H).comp (continuous_const.prodMk (continuous_id.prodMk continuous_id))))
  have split (k : Record N H) : G (paste H k) =
      q k.1 k.2.1*q k.1 k.2.2*Real.exp (crossEnergy (crossMatrix H A) k.2.1 k.2.2) := by
    rcases k with ⟨b,u,v⟩
    have hf := half _ _ (paste_left H b u v)
    have hg := half (paste H (b,u,v) ∘ H.refl) (paste H (b,v,v)) (paste_right H b u v)
    simp only [G,q,energy_split H A hs hr,Real.exp_add,hf,hg]
    ring
  have hg : 0 ≤ ∫ s, G s ∂prior N T := by
    rw [← (paste_preserving (N:=N) H).hasLaw.integral_comp hG.aestronglyMeasurable]
    rw [integral_prod _ ((hG.comp (paste_continuous H)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    apply integral_nonneg
    intro b
    change (0 : ℝ) ≤ ∫ y : Config N H.Plus × Config N H.Plus,
      G (paste H (b,y)) ∂((prior N H.Plus).prod (prior N H.Plus))
    simp_rw [split]
    exact cross_integral (crossMatrix H A) hK (q b) (hq b)
  change 0 ≤ ∫ s, F s*F (s ∘ H.refl) ∂((prior N T).tilted (energy A))
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  exact div_nonneg hg (integral_nonneg fun _ => (Real.exp_pos _).le)

private theorem sum_integral {N : ℕ} {T I : Type*} [Fintype T] [Fintype I]
    (μ : Measure (Config N T)) [IsFiniteMeasure μ] (f : I → Config N T → ℝ)
    (hc : ∀ i, Continuous (f i)) :
    (∫ s, ∑ i, f i s ∂μ) = ∑ i, ∫ s, f i s ∂μ :=
  integral_finsetSum _ (fun i _ => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- Any finite signed list of sites in the closed half, with its physical
normalized rotor dot correlations on the very same periodic coupling. -/
theorem dotPair_reflected_nonneg (N : ℕ) [NeZero N] {T : Type*} [Fintype T]
    (H : Half T) (A : T → T → ℝ) (hs : ∀ x y, A x y=A y x)
    (hr : ∀ x y, A (H.refl x) (H.refl y)=A x y) (hK : (crossMatrix H A).PosSemidef)
    {I : Type*} [Fintype I] (x : I → T) (hx : ∀ i, H.closed (x i)) (c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*dotPair N A (x i) (H.refl (x j)) := by
  let U (s : Config N T) := ∑ i, c i • (s (x i)).val
  have hcU : Continuous U := by unfold U; fun_prop
  have huk (k : Fin N) : Continuous (fun s => U s k) := by fun_prop
  have hθ : Continuous (fun s : Config N T => s ∘ H.refl) := continuous_pi fun a => continuous_apply _
  let μ : Measure (Config N T) := sphereGibbs N A
  have hk (k : Fin N) : 0 ≤ ∫ s, U s k * U (s ∘ H.refl) k ∂μ := by
    apply sphereGibbs_reflected_test N H A hs hr hK ⟨_,huk k⟩
    intro s t he
    have eq : U s=U t := Finset.sum_congr rfl fun i _ => by rw [he (x i) (hx i)]
    change U s k = U t k
    rw [eq]
  have hi : 0 ≤ ∫ s, ⟪U s,U (s ∘ H.refl)⟫_ℝ ∂μ := by
    simp only [PiLp.inner_apply,Real.inner_apply]
    rw [sum_integral μ (fun k s => U s k*U (s ∘ H.refl) k) (fun k => (huk k).mul ((huk k).comp hθ))]
    exact Finset.sum_nonneg fun k _ => hk k
  let B (i j : I) (s : Config N T) := c i*c j*⟪(s (x i)).val,(s (H.refl (x j))).val⟫_ℝ
  have hB (i j : I) : Continuous (B i j) := by unfold B; fun_prop
  have expand (s : Config N T) : ⟪U s,U (s ∘ H.refl)⟫_ℝ = ∑ i, ∑ j, B i j s := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [U, B, sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Function.comp_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [expand] at hi
  rw [sum_integral μ (fun i s => ∑ j, B i j s) (fun i => continuous_finsetSum _ (fun j _ => hB i j))] at hi
  simp_rw [sum_integral μ (B _) (hB _)] at hi
  simpa only [B,integral_const_mul,gibbs_integral_dot,μ] using hi

/-- A closed-half signed two-point observable of the complete physical
spin field; the lattice reflection may be affine. -/
def fieldQuadratic (N : ℕ) {I : Type*} [Fintype I] (r : Site → Site)
    (x : I → Site) (c : I → ℝ) : C(SpinField N, ℝ) where
  toFun s := ∑ i, ∑ j, (c i*c j)*fieldDot N (x i) (r (x j)) s
  continuous_toFun := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (fieldDot N (x i) (r (x j))).continuous

private theorem integral_fieldQuadratic {N : ℕ} {I : Type*} [Fintype I] (r : Site → Site)
    (x : I → Site) (c : I → ℝ) (P : ProbabilityMeasure (SpinField N)) :
    (∫ s, fieldQuadratic N r x c s ∂(P : Measure _)) =
      ∑ i, ∑ j, c i*c j*(∫ s, fieldDot N (x i) (r (x j)) s ∂(P : Measure _)) := by
  let G (i j : I) (s : SpinField N) := c i*c j*fieldDot N (x i) (r (x j)) s
  have hc (i j : I) : Continuous (G i j) := continuous_const.mul (fieldDot N _ _).continuous
  change (∫ s, ∑ i, ∑ j, G i j s ∂(P : Measure _)) = _
  rw [integral_finsetSum _ (fun i _ =>
    (continuous_finsetSum _ (fun j _ => hc i j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hc _ j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [G,integral_const_mul]

private theorem pair_at_displacement {N : ℕ} (P : ProbabilityMeasure (SpinField N))
    (hp : ShiftInvariant P) (x y : Site) :
    (∫ s, fieldDot N x y s ∂(P : Measure _))=fieldPair P (x-y) := by
  unfold fieldPair
  rw [← (hp y).hasLaw.integral_comp (fieldDot N 0 (x-y)).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun s => ?_
  change ⟪(s x).val,(s y).val⟫_ℝ = ⟪(s (0+y)).val,(s ((x-y)+y)).val⟫_ℝ
  simp only [zero_add, sub_add_cancel]
  exact real_inner_comm _ _

theorem stationary_fieldQuadratic (N : ℕ) {I : Type*} [Fintype I] (r : Site → Site)
    (x : I → Site) (c : I → ℝ) (P : ProbabilityMeasure (SpinField N)) (hp : ShiftInvariant P) :
    (∫ s, fieldQuadratic N r x c s ∂(P : Measure _)) =
      ∑ i, ∑ j, c i*c j*fieldPair P (x i-r (x j)) := by
  simp only [integral_fieldQuadratic,pair_at_displacement P hp]

/-- Finite physical criteria at every possible origin; these give a
concrete route from a torus interaction to a rooted spin-field inequality. -/
def HasRootMirrors {T I : Type*} [Fintype T] (D : Site → T → T)
    (J : T → T → ℝ) (r : Site → Site) (x : I → Site) : Prop :=
  ∀ o : T, ∃ H : Half T, (∀ a b, J a b=J b a) ∧
    (∀ a b, J (H.refl a) (H.refl b)=J a b) ∧ (crossMatrix H J).PosSemidef ∧
    (∀ i, H.closed (D (x i) o)) ∧ ∀ i, H.refl (D (x i) o)=D (r (x i)) o

theorem rooted_fieldQuadratic_nonneg (N : ℕ) [NeZero N] {T I : Type*} [Fintype T] [Nonempty T]
    [Fintype I] (D : Site → T → T) (J : T → T → ℝ) (r : Site → Site) (x : I → Site)
    (c : I → ℝ) (hm : HasRootMirrors D J r x) :
    0 ≤ ∫ s, fieldQuadratic N r x c s ∂(rootedLaw N D J : Measure _) := by
  rw [rootedLaw_integral]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro o _
  obtain ⟨H,hs,hr,hK,hx,he⟩ := hm o
  have h := dotPair_reflected_nonneg N H J hs hr hK (fun i => D (x i) o) hx c
  simp_rw [he] at h
  let G (i j : I) (s : T → Spin N) := c i*c j*⟪(s (D (x i) o)).val,(s (D (r (x j)) o)).val⟫_ℝ
  have hc (i j : I) : Continuous (G i j) := by unfold G; fun_prop
  change 0 ≤ ∫ s, ∑ i, ∑ j, G i j s ∂(sphereGibbs N J : Measure _)
  rw [sum_integral _ (fun i s => ∑ j, G i j s) (fun i => continuous_finsetSum _ (fun j _ => hc i j))]
  simp_rw [sum_integral _ (G _) (hc _)]
  simpa only [G,integral_const_mul,gibbs_integral_dot] using h

/-- On an ordinary periodic subsequence the estimate holds for the actual
weak limit, with no a priori stationarity or reflection hypothesis on it. -/
theorem cubic_limit_reflected (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (P : ProbabilityMeasure (SpinField N))
    (hP : Filter.Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides n) (K n)))
      Filter.atTop (𝓝 P)) {I : Type*} [Fintype I] (r : Site → Site)
    (x : I → Site) (c : I → ℝ) (hm : ∀ᶠ n in Filter.atTop,
      HasRootMirrors (Seam.baseMove (L:=sides n)) (Seam.ordinarySeries (sides n) (K n)) r x) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair P (x i-r (x j)) := by
  have hp : ShiftInvariant P := ShiftInvariant.of_tendsto hP (fun n =>
    rootedLaw_invariant N _ (Seam.cubic_displacement_action (sides n)) _)
  rw [←stationary_fieldQuadratic N r x c P hp]
  let F := fieldQuadratic N r x c
  apply ge_of_tendsto ((ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hP)
  filter_upwards [hm] with n hn
  exact rooted_fieldQuadratic_nonneg N _ _ r x c hn

/-- Read the same fully quantified finite inequalities through the two
actual limits in AdaptedVariationLimit, even when each inner subsequence
depends on the perturbation. -/
theorem adapted_variation_reflected (N : ℕ) {sides : ℕ → ℕ} [∀ n, NeZero (sides n)]
    [NeZero N] (K : ℕ → Site → ℝ) (Q : ProbabilityMeasure (SpinField N))
    (hQ : AdaptedVariationLimit N sides K Q) {I : Type*} [Fintype I] (r : Site → Site)
    (x : I → Site) (c : I → ℝ) (hm : ∀ᶠ n in Filter.atTop, ∀ᶠ l in Filter.atTop,
      HasRootMirrors (Seam.adaptedDestination (L:=sides l)) (Seam.adaptedSeries (sides l) (K n)) r x) :
    0 ≤ ∑ i, ∑ j, c i*c j*fieldPair Q (x i-r (x j)) := by
  obtain ⟨v,hv,w,P,hinner,houter⟩ := hQ
  have hstat (n : ℕ) : ShiftInvariant (P n) := ShiftInvariant.of_tendsto (hinner n).2 (fun j =>
    rootedLaw_invariant N _ (Seam.adapted_displacement_action (sides (w n j))) _)
  have hqstat : ShiftInvariant Q := ShiftInvariant.of_tendsto houter hstat
  rw [←stationary_fieldQuadratic N r x c Q hqstat]
  let F := fieldQuadratic N r x c
  apply ge_of_tendsto ((ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp houter)
  filter_upwards [hv.tendsto_atTop.eventually hm] with n hn
  apply ge_of_tendsto ((ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp (hinner n).2)
  filter_upwards [(hinner n).1.tendsto_atTop.eventually hn] with j hj
  exact rooted_fieldQuadratic_nonneg N _ _ r x c hj

end IsingScaling.Rotor.PressureSelection.PeriodicGibbsReflection

#print axioms IsingScaling.Rotor.PressureSelection.PeriodicGibbsReflection.sphereGibbs_reflected_test
#print axioms IsingScaling.Rotor.PressureSelection.PeriodicGibbsReflection.dotPair_reflected_nonneg
#print axioms IsingScaling.Rotor.PressureSelection.PeriodicGibbsReflection.cubic_limit_reflected
#print axioms IsingScaling.Rotor.PressureSelection.PeriodicGibbsReflection.adapted_variation_reflected
