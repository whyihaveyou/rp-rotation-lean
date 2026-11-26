import MathlibProbe.RotorPeriodicGibbsReflection

/-! # The horizontal symmetry of the original periodic sphere-spin laws

Sign changes of any of the three coordinates and interchange of the
first two coordinates descend to both physical periodic lattices. For
the oblique torus, period vectors are L times integer triples whose
first two coordinates have the same parity. This description is
unchanged by each of the sixteen transformations.

Reindexing a spin configuration permutes independent copies of the same
surface probability. The energy of a symmetric displacement coupling is
unchanged after reindexing, so its normalized Gibbs expectations, its
uniformly rooted field, and weak limits of those expectations inherit
the corresponding symmetry. On the Fourier side the real characters
transform contragrediently. Their orbit averages can therefore be
integrated against the original representing law directly.
-/

noncomputable section
open scoped Classical Topology InnerProductSpace
open Finset MeasureTheory Filter
namespace IsingScaling.Rotor.PressureSelection.PeriodicHorizontal

def perm (b : Bool) : Equiv.Perm (Fin 3) := if b then Equiv.swap 0 1 else Equiv.refl _
def action (a : HorizontalSymmetry) := signedPerm (perm a.2) a.1

theorem action_apply (a : HorizontalSymmetry) (z : Site) (i : Fin 3) :
    action a z i = if a.1 i then -(z (perm a.2 i)) else z (perm a.2 i) := rfl

private theorem action_add (a : HorizontalSymmetry) (x y : Site) :
    action a (x+y)=action a x+action a y := by
  funext i
  simp only [Pi.add_apply,action_apply]
  split <;> ring

private theorem action_smul (a : HorizontalSymmetry) (n : ℤ) (x : Site) :
    action a (n • x)=n • action a x := by
  funext i
  simp only [Pi.smul_apply,action_apply,smul_eq_mul]
  split <;> ring

private theorem action_sub (a : HorizontalSymmetry) (x y : Site) :
    action a (x-y)=action a x-action a y := by
  funext i
  simp only [Pi.sub_apply,action_apply]
  split <;> ring

/-- The first two coordinates of an adapted period, divided by its size,
agree modulo two. This characterizes every winding sector. -/
private theorem adapted_period (L : ℕ) (x y : Site) :
    Seam.SamePeriodClass L x y ↔
      ∃ k : Site, x-y=(L:ℤ) • k ∧ k 0 % 2 = k 1 % 2 := by
  constructor
  · rintro ⟨i,j,l,hx,hy,hz⟩
    refine ⟨![2*i+j,j,l], ?_, by simp⟩
    funext n
    fin_cases n
    · change x 0 - y 0 = (L:ℤ)*(2*i+j)
      linear_combination hx
    · exact hy
    · exact hz
  · rintro ⟨k,h,he⟩
    have hh : k 0-k 1=2*((k 0-k 1)/2) := by omega
    refine ⟨(k 0-k 1)/2,k 1,k 2,?_,congrFun h 1,congrFun h 2⟩
    have hx := congrFun h 0
    change x 0-y 0 = (L:ℤ)*k 0 at hx
    linear_combination hx + (L:ℤ)*hh

private theorem same_parity (a : HorizontalSymmetry) (k : Site)
    (h : k 0 % 2 = k 1 % 2) : action a k 0 % 2 = action a k 1 % 2 := by
  rcases a with ⟨s,b⟩
  cases b <;> cases h0 : s 0 <;> cases h1 : s 1 <;>
    simp [action_apply,perm,h0,h1] <;> omega

private theorem inverse_symmetry (a : HorizontalSymmetry) :
    ∃ b, (action a).symm=action b := by
  rcases a with ⟨s,b⟩
  refine ⟨(fun i => s ((perm b).symm i),b),?_⟩
  apply Equiv.ext
  intro x
  funext i
  cases b <;> rfl

private theorem adapted_period_map (L : ℕ) (a : HorizontalSymmetry) (x y : Site)
    (h : Seam.SamePeriodClass L x y) : Seam.SamePeriodClass L (action a x) (action a y) := by
  rw [adapted_period] at h ⊢
  obtain ⟨k,hk,hp⟩ := h
  exact ⟨action a k,by rw [←action_sub,hk,action_smul],same_parity a k hp⟩

private theorem cubic_period (L : ℕ) (x y : Site) :
    CubicSeam.coords L x = CubicSeam.coords L y ↔ ∃ k : Site, x-y=(L:ℤ) • k := by
  change ((x 0 : ZMod L),(x 1 : ZMod L),(x 2 : ZMod L)) =
    ((y 0 : ZMod L),(y 1 : ZMod L),(y 2 : ZMod L)) ↔ _
  have he (i : Fin 3) : ((x i:ZMod L)=(y i:ZMod L)) ↔ ∃ j, x i-y i=(L:ℤ)*j := by
    rw [eq_comm,ZMod.intCast_eq_intCast_iff_dvd_sub]
    rfl
  simp only [Prod.mk.injEq,he]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩⟩
    exact ⟨![i,j,k],funext fun n => by fin_cases n <;> assumption⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨_,congrFun hk 0⟩,⟨_,congrFun hk 1⟩,⟨_,congrFun hk 2⟩⟩

/-- A finite site set with its actual lattice projection and displacement. -/
private structure Chart {T : Type*} (D : Site → T → T) where
  project : Site → T
  onto : Function.Surjective project
  step : ∀ z x, project (x+z)=D z (project x)
  respects : ∀ a : HorizontalSymmetry, ∀ x y, project x=project y →
    project (action a x)=project (action a y)

private def adaptedChart (L : ℕ) [NeZero L] :
    Chart (Seam.adaptedDestination (L:=L)) where
  project x := (DiagonalSeam.siteEquiv L).symm (DiagonalSeam.coords L x)
  onto t := ⟨Seam.representative t,(DiagonalSeam.siteEquiv L).symm_apply_apply t⟩
  step z x := by
    apply (DiagonalSeam.siteEquiv L).injective
    rw [Equiv.apply_symm_apply]
    change _=DiagonalSeam.siteCoords (Seam.adaptedDestination _ _)
    rw [DiagonalSeam.coords_adaptedDestination,DiagonalSeam.coords_add]
    congr 1
    exact ((DiagonalSeam.siteEquiv L).apply_symm_apply _).symm
  respects a x y h := by
    apply congrArg (DiagonalSeam.siteEquiv L).symm
    apply (DiagonalSeam.samePeriod_iff_coords L _ _).mp
    exact adapted_period_map L a x y ((DiagonalSeam.samePeriod_iff_coords L _ _).mpr
      ((DiagonalSeam.siteEquiv L).symm.injective h))

private def cubicChart (L : ℕ) [NeZero L] : Chart (Seam.baseMove (L:=L)) where
  project x := (CubicSeam.cubeEquiv L).symm (CubicSeam.coords L x)
  onto t := ⟨![(t.1.val:ℤ),t.2.1.val,t.2.2.val],by
    apply (CubicSeam.cubeEquiv L).injective
    rw [Equiv.apply_symm_apply]
    simp [CubicSeam.cubeEquiv,CubicSeam.coords,CubicSeam.cubeCoords]⟩
  step z x := by
    apply (CubicSeam.cubeEquiv L).injective
    rw [Equiv.apply_symm_apply]
    change _=CubicSeam.cubeCoords (Seam.baseMove _ _)
    rw [CubicSeam.cubeCoords_baseMove]
    change _=(CubicSeam.cubeEquiv L) ((CubicSeam.cubeEquiv L).symm _) + _
    rw [Equiv.apply_symm_apply]
    simp [CubicSeam.coords]
  respects a x y h := by
    apply congrArg (CubicSeam.cubeEquiv L).symm
    obtain ⟨k,hk⟩ := (cubic_period L x y).mp ((CubicSeam.cubeEquiv L).symm.injective h)
    exact (cubic_period L _ _).mpr ⟨action a k,by rw [←action_sub,hk,action_smul]⟩

private def Chart.induced {T : Type*} {D : Site → T → T} (V : Chart D)
    (a : HorizontalSymmetry) (t : T) : T := V.project (action a (V.onto t).choose)

private theorem Chart.induced_project {T : Type*} {D : Site → T → T} (V : Chart D)
    (a : HorizontalSymmetry) (x : Site) : V.induced a (V.project x)=V.project (action a x) :=
  V.respects a _ _ (V.onto (V.project x)).choose_spec

private def Chart.equiv {T : Type*} [Fintype T] {D : Site → T → T} (V : Chart D)
    (a : HorizontalSymmetry) : T ≃ T := by
  apply Equiv.ofBijective (V.induced a)
  apply (Finite.injective_iff_bijective).mp
  intro t u h
  obtain ⟨s,rfl⟩ := V.onto t
  obtain ⟨v,rfl⟩ := V.onto u
  simp only [V.induced_project] at h
  obtain ⟨b,hb⟩ := inverse_symmetry a
  have hh := V.respects b _ _ h
  simpa only [← hb,Equiv.symm_apply_apply] using hh

private theorem Chart.equiv_move {T : Type*} [Fintype T] {D : Site → T → T} (V : Chart D)
    (a : HorizontalSymmetry) (z : Site) (t : T) :
    V.equiv a (D z t)=D (action a z) (V.equiv a t) := by
  obtain ⟨x,rfl⟩ := V.onto t
  change V.induced a (D z (V.project x))=D _ (V.induced a (V.project x))
  rw [←V.step,V.induced_project,V.induced_project,action_add,V.step]

theorem cubic_reindex (L : ℕ) [NeZero L] (a : HorizontalSymmetry) :
    ∃ e : Seam.Cell L ≃ Seam.Cell L, ∀ z v, e (Seam.baseMove z v)=Seam.baseMove (action a z) (e v) :=
  ⟨(cubicChart L).equiv a,(cubicChart L).equiv_move a⟩

theorem adapted_reindex (L : ℕ) [NeZero L] (a : HorizontalSymmetry) :
    ∃ e : Seam.Site L ≃ Seam.Site L, ∀ z v, e (Seam.adaptedDestination z v)=
      Seam.adaptedDestination (action a z) (e v) :=
  ⟨(adaptedChart L).equiv a,(adaptedChart L).equiv_move a⟩

private theorem signed_apply (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (z : Site) (i : Fin 3) :
    signedPerm p s z i = if s i then -(z (p i)) else z (p i) := rfl

private theorem signed_add (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (x z : Site) :
    signedPerm p s (x+z)=signedPerm p s x + signedPerm p s z := by
  funext i
  simp only [Pi.add_apply,signed_apply]
  split <;> ring

private theorem cubic_descent (L : ℕ) [NeZero L] (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    {x y : Site} (h : (cubicChart L).project x = (cubicChart L).project y) :
    (cubicChart L).project (signedPerm p s x)=(cubicChart L).project (signedPerm p s y) := by
  apply congrArg (CubicSeam.cubeEquiv L).symm
  obtain ⟨k,hk⟩ := (cubic_period L x y).mp ((CubicSeam.cubeEquiv L).symm.injective h)
  apply (cubic_period L _ _).mpr
  refine ⟨signedPerm p s k,funext fun i => ?_⟩
  have he := congrFun hk (p i)
  change x (p i) - y (p i) = (L:ℤ)*k (p i) at he
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,signed_apply]
  split
  · linear_combination -he
  · exact he

/-- The ordinary periodic torus admits all signed coordinate permutations,
including permutations interchanging the third direction with the others. -/
theorem cubic_reindex_signed (L : ℕ) [NeZero L] (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∃ e : Seam.Cell L ≃ Seam.Cell L, ∀ z v, e (Seam.baseMove z v)=Seam.baseMove (signedPerm p s z) (e v) := by
  let V := cubicChart L
  let f (v : Seam.Cell L) := V.project (signedPerm p s (V.onto v).choose)
  have hf (x : Site) : f (V.project x)=V.project (signedPerm p s x) :=
    cubic_descent L p s (V.onto (V.project x)).choose_spec
  have hin : Function.Injective f := by
    intro u v h
    obtain ⟨x,rfl⟩ := V.onto u
    obtain ⟨y,rfl⟩ := V.onto v
    rw [hf,hf] at h
    have he : (signedPerm p s).symm = signedPerm p.symm (fun i => s (p.symm i)) := by
      apply Equiv.ext
      intro z
      rfl
    have hh := cubic_descent L p.symm (fun i => s (p.symm i)) h
    simpa only [←he,Equiv.symm_apply_apply] using hh
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hin),?_⟩
  intro z v
  obtain ⟨x,rfl⟩ := V.onto v
  change f (Seam.baseMove z (V.project x))=Seam.baseMove _ (f (V.project x))
  rw [← V.step,hf,signed_add,V.step,hf]

theorem periodized_reindex {T : Type*} [DecidableEq T] (D : Site → T → T)
    (g : Site ≃ Site) (e : T ≃ T) (he : ∀ z v, e (D z v)=D (g z) (e v))
    (J : Site → ℝ) (hJ : ∀ z,J (g z)=J z) (v w : T) :
    Seam.periodizeSeries D J (e v) (e w)=Seam.periodizeSeries D J v w := by
  unfold Seam.periodizeSeries
  rw [←g.tsum_eq (fun z => if D z (e v)=e w then J z else 0)]
  apply tsum_congr
  intro z
  simp only [←he,hJ,e.injective.eq_iff]

private def spinMove {T : Type*} (N : ℕ) (e : T ≃ T) : C(T → Spin N,T → Spin N) where
  toFun s := s ∘ e
  continuous_toFun := continuous_pi fun i => continuous_apply (e i)

private theorem energy_move {T : Type*} [Fintype T] {N : ℕ} (A : T → T → ℝ)
    (e : T ≃ T) (hA : ∀ v w, A (e v) (e w)=A v w) (s : T → Spin N) :
    energy A (spinMove N e s)=energy A s := by
  let f (x y : T) := A x y*⟪(s x).val,(s y).val⟫_ℝ
  have he : (∑ v, ∑ w, f (e v) (e w)) = ∑ v, ∑ w, f v w := by
    calc
      _ = ∑ v, ∑ w, f (e v) w := Finset.sum_congr rfl fun v _ => e.sum_comp (f (e v))
      _ = _ := e.sum_comp (fun v => ∑ w, f v w)
  unfold energy
  congr 1
  simpa only [f,hA,spinMove,ContinuousMap.coe_mk,Function.comp_apply] using he

/-- Reindexing the actual finite Gibbs configuration preserves its
complete probability law whenever the real coupling matrix is invariant. -/
theorem sphereGibbs_reindex (N : ℕ) [NeZero N] {T : Type*} [Fintype T] (A : T → T → ℝ)
    (e : T ≃ T) (hA : ∀ v w,A (e v) (e w)=A v w) :
    MeasurePreserving (fun s : T → Spin N => s ∘ e)
      (sphereGibbs N A : Measure _) (sphereGibbs N A : Measure _) := by
  let τ := Measure.pi (fun _ : T => SiteReflection.surfacePrior N)
  have hp : MeasurePreserving (spinMove N e) τ τ := by
    have h := measurePreserving_piCongrLeft (fun _ : T => SiteReflection.surfacePrior N) e.symm
    convert h using 1
    funext s x
    change s (e x)=(e.symm.piCongrLeft (fun _ => Spin N)) s x
    simp [Equiv.piCongrLeft_apply]
  have hc : Continuous (energy (N:=N) A) := by unfold energy; fun_prop
  let move := spinMove N e
  refine ⟨move.continuous.measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ x, F x ∂Measure.map move (sphereGibbs N A : Measure _))=_
  rw [integral_map move.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  change (∫ s, F (move s) ∂(τ.tilted (energy A)))=∫ s,F s ∂(τ.tilted (energy A))
  simp only [integral_tilted,smul_eq_mul,div_mul_eq_mul_div,integral_div]
  congr 1
  have h : (∫ s, Real.exp (energy A (spinMove N e s))*F (spinMove N e s) ∂τ)=
      ∫ s, Real.exp (energy A s)*F s ∂τ :=
    hp.hasLaw.integral_comp (hc.rexp.mul F.continuous).aestronglyMeasurable
  simpa only [energy_move A e hA] using h

def fieldAction (N : ℕ) (g : Site ≃ Site) : C(SpinField N,SpinField N) where
  toFun σ := σ ∘ g
  continuous_toFun := continuous_pi fun x => continuous_apply (g x)

def FixedBy {N : ℕ} (P : ProbabilityMeasure (SpinField N)) (g : Site ≃ Site) : Prop :=
  MeasurePreserving (fieldAction N g) (P : Measure _) (P : Measure _)

def StateInvariant {N : ℕ} (P : ProbabilityMeasure (SpinField N)) :=
  ∀ a : HorizontalSymmetry, FixedBy P (action a)

def InvariantProfile (J : Site → ℝ) := ∀ a : HorizontalSymmetry, ∀ z, J (action a z)=J z

private theorem fixed_of_integrals {N : ℕ} (P : ProbabilityMeasure (SpinField N)) (g : Site ≃ Site)
    (h : ∀ F : C(SpinField N,ℝ),
      (∫ s,(F.comp (fieldAction N g)) s ∂(P : Measure _))=∫ s,F s ∂(P : Measure _)) :
    FixedBy P g := by
  refine ⟨(fieldAction N g).continuous.measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (fieldAction N g).continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact h F.toContinuousMap

/-- No symmetrization of distinct weak states is needed. Each whole
uniformly rooted finite-periodic law already has the physical symmetry. -/
theorem rooted_fixed (N : ℕ) [NeZero N] {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (D : Site → T → T) (g : Site ≃ Site) (e : T ≃ T) (he : ∀ z v,e (D z v)=D (g z) (e v))
    (J : Site → ℝ) (hJ : ∀z,J (g z)=J z) :
    FixedBy (rootedLaw N D (Seam.periodizeSeries D J)) g := by
  apply fixed_of_integrals
  intro F
  rw [rootedLaw_integral,rootedLaw_integral]
  let A := Seam.periodizeSeries D J
  let μ : Measure (T → Spin N) := sphereGibbs N A
  have hμ := sphereGibbs_reindex N A e (periodized_reindex D g e he J hJ)
  congr 1
  rw [← e.sum_comp (fun v => ∫ s,(F.comp (fieldAction N g)) (liftAt D v s) ∂μ)]
  apply Finset.sum_congr rfl
  intro v _
  let f (s : T → Spin N) := F (liftAt D v s)
  have hf : Continuous f := F.continuous.comp (continuous_pi fun z => continuous_apply _)
  have hspin (s : T → Spin N) : fieldAction N g (liftAt D (e v) s)=liftAt D v (s ∘ e) := by
    funext z
    change s (D (g z) (e v))=s (e (D z v))
    rw [he]
  simp only [ContinuousMap.comp_apply,hspin]
  change (∫ s, f (s ∘ e) ∂μ)=∫ s,f s ∂μ
  exact hμ.hasLaw.integral_comp hf.aestronglyMeasurable

theorem fixed_of_tendsto {N : ℕ} {P : ℕ → ProbabilityMeasure (SpinField N)}
    {Q : ProbabilityMeasure (SpinField N)} (h : Tendsto P atTop (𝓝 Q)) (g : Site ≃ Site)
    (hs : ∀ᶠ n in atTop, FixedBy (P n) g) : FixedBy Q g := by
  apply fixed_of_integrals
  intro F
  have h₁ := (ProbabilityMeasure.continuous_integral_continuousMap
    (F.comp (fieldAction N g))).continuousAt.tendsto.comp h
  have h₂ := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp h
  apply tendsto_nhds_unique (h₁.congr' _) h₂
  filter_upwards [hs] with n hn
  exact hn.hasLaw.integral_comp F.continuous.aestronglyMeasurable

theorem cubic_limit_invariant (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides n) (K n))) atTop (𝓝 P))
    (hK : ∀ᶠ n in atTop, InvariantProfile (K n)) : StateInvariant P := by
  intro a
  apply fixed_of_tendsto hP
  filter_upwards [hK] with n hn
  obtain ⟨e,he⟩ := cubic_reindex (sides n) a
  exact rooted_fixed N _ _ e he _ (hn a)

theorem cubic_limit_signed (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides n) (K n))) atTop (𝓝 P))
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (hK : ∀ᶠ n in atTop, ∀ z,
      K n (signedPerm p s z)=K n z) : FixedBy P (signedPerm p s) := by
  apply fixed_of_tendsto hP
  filter_upwards [hK] with n hn
  obtain ⟨e,he⟩ := cubic_reindex_signed (sides n) p s
  exact rooted_fixed N _ _ e he _ hn

theorem adapted_limit_invariant (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (Q : ProbabilityMeasure (SpinField N)) (hQ : AdaptedVariationLimit N sides K Q)
    (hK : ∀ᶠ n in atTop, InvariantProfile (K n)) : StateInvariant Q := by
  obtain ⟨v,hv,w,P,hinner,houter⟩ := hQ
  intro a
  apply fixed_of_tendsto houter
  filter_upwards [hv.tendsto_atTop.eventually hK] with n hn
  apply fixed_of_tendsto (hinner n).2
  apply Eventually.of_forall
  intro j
  obtain ⟨e,he⟩ := adapted_reindex (sides (w n j)) a
  exact rooted_fixed N _ _ e he _ (hn a)

theorem pair_fixed {N : ℕ} {P : ProbabilityMeasure (SpinField N)} {g : Site ≃ Site}
    (hf : FixedBy P g) (hg : g 0=0) (z : Site) : fieldPair P (g z)=fieldPair P z := by
  have h := hf.hasLaw.integral_comp (fieldDot N 0 z).continuous.aestronglyMeasurable
  have he (s : SpinField N) : fieldDot N 0 z (fieldAction N g s)=fieldDot N 0 (g z) s := by
    change ⟪(s (g 0)).val,(s (g z)).val⟫_ℝ=_
    rw [hg]
    rfl
  simpa only [Function.comp_apply,he,fieldPair] using h

theorem cubic_limit_pair_signedPerm (N : ℕ) [NeZero N] (sides : ℕ → ℕ) [∀ n, NeZero (sides n)]
    (K : ℕ → Site → ℝ) (P : ProbabilityMeasure (SpinField N))
    (hP : Tendsto (fun n => rootedLaw N Seam.baseMove (Seam.ordinarySeries (sides n) (K n))) atTop (𝓝 P))
    (p : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (hK : ∀ᶠ n in atTop, ∀ z,
      K n (signedPerm p s z)=K n z) (z : Site) : fieldPair P (signedPerm p s z)=fieldPair P z :=
  pair_fixed (cubic_limit_signed N sides K P hP p s hK) (signedPerm_zero p s) z

theorem character_action (a : HorizontalSymmetry) (z : Site) (k : Momentum) :
    realCharacter (action a z) (horizontalAction a k)=realCharacter z k := by
  have he (i : Fin 3) : (horizontalAction a k i) ^ (action a z i)=
      (k (perm a.2 i))^(z (perm a.2 i)) := by
    change (if a.1 i then (k (perm a.2 i))⁻¹ else k (perm a.2 i)) ^
      (if a.1 i then -(z (perm a.2 i)) else z (perm a.2 i))=_
    cases a.1 i <;> simp
  have hp : (∏ i, (horizontalAction a k i) ^ (action a z i))=∏ i,k i^(z i) := by
    simp only [he]
    exact Equiv.prod_comp (perm a.2) (fun i => k i^(z i))
  exact congrArg (fun u : Circle => (u : ℂ).re) hp

private theorem continuous_action (a : HorizontalSymmetry) : Continuous (horizontalAction a) := by
  apply continuous_pi
  intro i
  change Continuous (fun k : Momentum => if a.1 i then (k (perm a.2 i))⁻¹ else k (perm a.2 i))
  split <;> fun_prop

/-- For an arbitrary Fourier representative of the same physical field, the
stabilizer mean of this actual signed packet has exactly its original
expectation. No uniqueness of Fourier measures from the real characters
is needed. -/
theorem integral_mean_reflected_eq {N : ℕ} (P : ProbabilityMeasure (SpinField N)) (hP : StateInvariant P)
    (μ : ProbabilityMeasure Momentum) (hμ : ∀ z, spectralPair (μ : Measure _) z=fieldPair P z)
    {I : Type*} [Fintype I] (r : Site → Site) (x : I → Site) (c : I → ℝ) :
    (∫ k,horizontalMean (reflectedTest r x c) k ∂(μ : Measure _))=
      ∫ k,reflectedTest r x c k ∂(μ : Measure _) := by
  have hchar (a : HorizontalSymmetry) (z : Site) :
      (∫ k, realCharacter z (horizontalAction a k) ∂(μ : Measure _))=fieldPair P z := by
    have eq (k : Momentum) : realCharacter z (horizontalAction a k)=
        realCharacter ((action a).symm z) k := by
      simpa only [Equiv.apply_symm_apply] using character_action a ((action a).symm z) k
    simp_rw [eq]
    change spectralPair (μ : Measure _) _=_
    rw [hμ]
    simpa only [Equiv.apply_symm_apply] using
      (pair_fixed (hP a) (signedPerm_zero _ _) ((action a).symm z)).symm
  let T := reflectedTest r x c
  have he (a : HorizontalSymmetry) :
      (∫ k, T (horizontalAction a k) ∂(μ : Measure _))=∫ k,T k ∂(μ : Measure _) := by
    rw [integral_reflectedTest]
    let G (i j : I) (k : Momentum) := c i*c j*realCharacter (x i-r (x j)) (horizontalAction a k)
    have hc (i j : I) : Continuous (G i j) := continuous_const.mul
      ((realCharacter _).continuous.comp (continuous_action a))
    change (∫ k, ∑ i, ∑ j,G i j k ∂(μ : Measure _))=_
    rw [integral_finsetSum _ (fun i _ => (continuous_finsetSum _ (fun j _ => hc i j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp_rw [integral_finsetSum _ (fun j _ => (hc _ j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    simp only [G,integral_const_mul,hchar,hμ]
  change (∫ k,(∑ a : HorizontalSymmetry, T (horizontalAction a k))/Fintype.card HorizontalSymmetry
    ∂(μ : Measure _))=_
  have hi (a : HorizontalSymmetry) : Integrable (fun k => T (horizontalAction a k)) (μ : Measure _) :=
    (T.continuous.comp (continuous_action a)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_div,integral_finsetSum _ (fun a _ => hi a)]
  simp only [he,sum_const,card_univ,nsmul_eq_mul]
  field_simp
  rfl

end IsingScaling.Rotor.PressureSelection.PeriodicHorizontal

#print axioms IsingScaling.Rotor.PressureSelection.PeriodicHorizontal.sphereGibbs_reindex
#print axioms IsingScaling.Rotor.PressureSelection.PeriodicHorizontal.cubic_limit_signed
#print axioms IsingScaling.Rotor.PressureSelection.PeriodicHorizontal.adapted_limit_invariant
#print axioms IsingScaling.Rotor.PressureSelection.PeriodicHorizontal.integral_mean_reflected_eq
