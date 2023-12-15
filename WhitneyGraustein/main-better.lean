import Mathlib
import WhitneyGraustein.calculus


open Set Function Complex Real Order

open Topology NormedSpace

open Mathlib



noncomputable section

structure CircleImmersion (γ : ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ γ
  per : Periodic γ 1
  deriv_ne : ∀ t, deriv γ t ≠ 0

/- If extra time, prove existence of lift and convert axioms to defs/lemmas -/

/-
structure CircleImmersion.lift (θ : ℝ → ℝ) : Prop where
  θ : ℝ → ℝ ???
  diff : ContDiff ℝ ⊤ θ
  expr : ∀ t, (deriv γ t = ‖deriv γ t‖ * exp (I * θ t))
-/

def CircleImmersion.lift {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) : ℝ → ℝ := sorry
/-MAKE SURE THE PERIODIC SHOULD BE DEFINED AND NOT PROVEN-/
lemma lift_exists {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) :
  ∃ θ : ℝ → ℝ, (θ = CircleImmersion.lift imm_γ) ∧ (ContDiff ℝ ⊤ θ) ∧ (∀ (t : ℝ), (deriv γ t = ‖deriv γ t‖ * exp (I * θ t))) ∧ (Periodic θ 1) := sorry

-- Lift unique?


variable {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ)

axiom CircleImmersion.contDiff_lift : ContDiff ℝ ⊤ imm_γ.lift

axiom CircleImmersion.deriv_eq (t : ℝ) : deriv γ t = ‖deriv γ t‖ * Complex.exp (I * imm_γ.lift t)



noncomputable def CircleImmersion.turningNumber := (imm_γ.lift 1 - imm_γ.lift 0) / (2 * π)

structure HtpyCircleImmersion (γ : ℝ → ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ (uncurry γ)
  imm : ∀ s, CircleImmersion (γ s)

/-
∀K₁, K₂, K₃ : ℝ, with K₁ > 0, and ∀H > 0, we claim that  there exists some N₀ such that N ≥ N₀
implies that K₁HN - K₂H - K₃ > 0

This is required to construct our gamma function and for the main phase.
-/

lemma root_lemma_maybe {H:ℝ} (K₁ : ℝ) (K₂ : ℝ) (K₃ : ℝ) (K₁_pos : K₁ > 0) (H_pos : H > 0) : ∃ (N₀ : ℕ), ∀ N > N₀, (K₁ * H) * N - (K₂ * H + K₃) > 0 := by
  let K₁H_pos := Real.mul_pos K₁_pos H_pos
  /- Claim that N₀ = max (⌊(K₃ + K₂ * H) / (K₁ * H) + 1⌋) (0)

  Note that:
  N₀ > (K₃ + K₂ * H) / (K₁ * H)
  ↔ K₁*HN > K₃ + K₂ * H
  ↔  K₁*HN - K₂ * H -  K₃ > 0
  -/
  let N₀ := Nat.floor (max ((K₃ + K₂ * H) / (K₁ * H) + 1) (0) )
  use N₀
  intro N hN

  have apply_floor_lt :=
    (Nat.floor_lt (le_max_right ((K₃ + K₂ * H) / (K₁ * H) + 1) 0)).1 (gt_iff_lt.1 hN)

  have context: (K₃ + K₂ * H) / (K₁ * H) + 1 ≤ max ((K₃ + K₂ * H) / (K₁ * H) + 1) 0 := by
    exact le_max_left ((K₃ + K₂ * H) / (K₁ * H) + 1) 0

  have final: (K₃ + K₂ * H) / (K₁ * H) < N := by linarith
  have final2: (K₃ + K₂ * H) < (K₁ * H) * N  := by exact (div_lt_iff' K₁H_pos).mp final
  linarith

namespace WhitneyGraustein

@[reducible] def unit : Set ℝ := Set.Icc 0 1
@[reducible] def ruffling : Set ℝ := Set.Icc 0 (1/4:ℝ)
@[reducible] def unruffling : Set ℝ := Set.Icc (3/4:ℝ) 1
@[reducible] def main : Set ℝ := Set.Icc (1/4:ℝ) (3/4:ℝ)
@[reducible] def antimain : Set ℝ := (Set.Iic 0) ∪ (Set.Ici 1)

lemma ruffling_closed : IsClosed (Set.Icc 0 (1/4:ℝ)) := isClosed_Icc
lemma unruffling_closed : IsClosed (Set.Icc (3/4:ℝ) 1) := isClosed_Icc
lemma main_closed : IsClosed (Set.Icc (1/4:ℝ) (3/4:ℝ)) := isClosed_Icc

lemma ruffling_unruffling_disjoint : Disjoint ruffling unruffling := by
  intro S hS hS'
  by_contra opp
  push_neg at opp

  rcases (not_forall_not.mp opp) with ⟨x,hx⟩
  specialize hS hx
  specialize hS' hx
  rcases hS with ⟨_,B⟩
  rcases hS' with ⟨C,_⟩
  have fact : (1/4:ℝ) < (3/4:ℝ) := by norm_num
  have fact2 : x < (3/4:ℝ)  := LE.le.trans_lt B fact
  linarith

lemma main_antimain_disjoint : Disjoint main antimain := by
  intro S hS hS'
  by_contra opp
  push_neg at opp

  rcases (not_forall_not.mp opp) with ⟨x,hx⟩
  specialize hS hx
  specialize hS' hx
  rcases hS with ⟨A,B⟩
  rcases hS' with C|D

  simp at C
  linarith
  simp at D
  linarith

lemma triangle' {A B : ℂ} : ‖B‖ ≤ ‖A + B‖ + ‖A‖ := by
  have fact := norm_add_le (A+B) (-A)
  simp at fact
  exact fact

lemma triangle {A B : ℂ} : ‖B‖ - ‖A‖ ≤ ‖A + B‖ :=
  tsub_le_iff_right.mpr triangle'

lemma in_particular {A B C : ℂ} : ‖C‖ - ‖B‖ - ‖A‖ ≤ ‖A + B + C‖ :=
  calc
    ‖C‖ - ‖B‖ - ‖A‖ ≤ ‖B + C‖ - ‖A‖ := sub_le_sub_right triangle ‖A‖
    _ ≤ ‖A + (B + C)‖ := triangle
    _ = ‖A + B + C‖ := congrArg Norm.norm (add_assoc A B C).symm


def H : ℝ := 1

lemma H_pos : 0 < H := Real.zero_lt_one

def h : ℝ → ℝ := sorry

lemma h_diff : ContDiff ℝ ⊤ h  := sorry

lemma h_main : ∀ᶠ (x : ℝ) in 𝓝ˢ main, h x = 0 := sorry

lemma h_antimain : ∀ᶠ (x : ℝ) in 𝓝ˢ antimain, h x = H := sorry

lemma h_mem : ∀ (x : ℝ), h x ∈ Icc 0 1 := sorry

@[simp] lemma h_zero : h 0 = 0 := sorry

@[simp] lemma h_one : h 1 = 0 := sorry


def ruffle : ℝ → ℂ := fun t ↦ ⟨-Real.sin (4 * π * t), 2 * Real.sin (2 * π * t)⟩

lemma duh : ruffle = (fun x:ℝ ↦ -Real.sin (4 * π * x)+ (2 * Real.sin (2 * π * x))•I) := by
  ext x
  unfold ruffle
  dsimp
  have fact (y:ℂ) : y=y.re + y.im • I := by
    simp
  specialize fact (ruffle x)
  unfold ruffle at fact
  dsimp at fact
  rw [fact]
  simp

lemma deriv_sin_local {f : ℝ → ℝ} {x : ℝ} (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.hasDerivAt.sin.deriv

lemma deriv_sin_local' (t : ℝ):
    -deriv (fun (x:ℝ) ↦ (↑(Real.sin (4 * π * x)):ℂ)) t = -↑(Real.cos (4 * π * t) * deriv (fun x ↦ 4 * π * x) t):= by
    refine ((fun {z w} ↦ Complex.ext_iff.mpr) ?_).symm


lemma ruffle_deriv_neq_zero_on_unit{t:ℝ}(ht: t ∈ unit): deriv ruffle t ≠ 0 := by
  rw[duh]

  intro opp

  rw [deriv_add] at opp
  rw [deriv.neg] at opp
  have := deriv_sin_local' t
  rw [this] at opp
  clear this

  have : ∀ k:ℝ, (deriv (fun (x:ℝ) ↦ k * x) t ) = k * deriv (fun (x:ℝ) ↦ x) t:= by
    intro k
    apply deriv_const_mul
    exact differentiableAt_id'
  specialize this (4*π)
  rw [this] at opp
  clear this
  simp only [deriv_id'', mul_one, real_smul, ofReal_sin,
    deriv_mul_const_field', deriv_const_mul_field'] at opp
  push_cast at opp
  rw [deriv_const_mul] at opp
  sorry









  /-TODO!!!!!! -/



/-Credit: Alex J. Best-/
lemma coer_diff : ContDiff ℝ ⊤ fun (x:ℝ) ↦ (x:ℂ) := by
  refine IsBoundedLinearMap.contDiff ?hf
  refine IsLinearMap.with_bound ?hf.hf 1 ?hf.h
  refine { map_add := ?hf.hf.map_add, map_smul := ?hf.hf.map_smul }
  simp
  simp
  simp



lemma ruffle_diff : ContDiff ℝ ⊤ ruffle := by
  rw [duh]

  apply ContDiff.add
  apply ContDiff.neg
  apply ContDiff.mul
  apply ContDiff.mul
  apply ContDiff.sub
  apply ContDiff.cexp
  apply ContDiff.mul
  apply ContDiff.neg
  apply ContDiff.mul
  exact contDiff_const

  exact coer_diff

  exact contDiff_const
  apply ContDiff.cexp
  apply ContDiff.mul
  apply ContDiff.mul
  exact contDiff_const

  exact coer_diff

  exact contDiff_const
  exact contDiff_const
  exact contDiff_const
  /-credit for this last part: Ruben Van de Velde-/
  simp only [smul_eq_mul]
  apply ContDiff.mul ?_ contDiff_const
  apply ContDiff.mul contDiff_const ?_
  simp_rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ←Complex.ofReal_sin]
  apply coer_diff.comp
  apply ContDiff.sin
  apply ContDiff.mul contDiff_const ?_
  apply contDiff_id










  /-FINISH!!!!!!!!!-/



def R : ℝ → ℂ := fun θ ↦ cexp (θ • I)

-- See https://github.com/leanprover-community/sphere-eversion/blob/master/SphereEversion/ToMathlib/Analysis/CutOff.lean
def ρ : ℝ → ℝ := sorry

lemma ρ_diff : ContDiff ℝ ⊤ ρ := sorry

lemma ρ_ruffling : EqOn ρ 0 ruffling := sorry

lemma ρ_unruffling : EqOn ρ 1 unruffling := sorry

lemma ρ_mem : ∀ x, ρ x ∈ Icc (0 : ℝ) 1 := sorry

@[simp] lemma rho_zero : ρ 0 = 0 := sorry

@[simp] lemma rho_one : ρ 1 = 1 := sorry


theorem whitney_graustein {γ₀ γ₁ : ℝ → ℂ} {t : ℝ} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁):
  (imm_γ₀.turningNumber = imm_γ₁.turningNumber) → ∃ (γ : ℝ → ℝ → ℂ), HtpyCircleImmersion γ ∧ ((∀ t, γ 0 t = γ₀ t) ∧ (∀ t, γ 1 t = γ₁ t)) := by
  intro hyp --we want to show that since there exists some N,H pair such that... then there exists...

  rcases (lift_exists imm_γ₀) with ⟨(θ₀ : ℝ → ℝ), hθ₀_lift_is_lift, hθ₀_diff, hθ₀_decomp, hθ₀_per⟩
  rcases (lift_exists imm_γ₁) with ⟨(θ₁ : ℝ → ℝ), hθ₁_lift_is_lift, hθ₁_diff, hθ₁_decomp, hθ₁_per⟩

  have fact {A : ℂ} : 0 = A + (-A) := by norm_num

  -- have critical : ∀ K₁ > 0, ∀ H > 0, ∀ N > N₀, ∀ s, ∀ t, ‖deriv (γ s) t‖ ≥ (K₁ s) * N * H - (K₂ s) * H - (K₃ s)
  -- fix γ₀, γ₁, and ρ
  -- ∀ H > 0, ∃ N₀, ∀ N ≥ N₀, K₁ * N * H - K₂ * H - K₃ > 0

  let ϝ  := fun s t ↦ (1 - (ρ s)) • (γ₀ t) + (ρ s) • γ₁ t
  let θ  := fun s t ↦ (1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t)



  let unit_compact : IsCompact unit := isCompact_Icc
  let unit_nonempty : Set.Nonempty unit := nonempty_of_nonempty_subtype

  let A := fun s t ↦ deriv (ϝ s) t
  let normA := fun s t ↦ ‖A s t‖


  have ϝ_diff : ContDiff ℝ ⊤ (uncurry ϝ) := by
    apply ContDiff.add
    apply ContDiff.smul
    apply ContDiff.sub
    exact contDiff_const
    exact ρ_diff.comp contDiff_fst
    exact imm_γ₀.diff.comp contDiff_snd
    apply ContDiff.smul
    exact ρ_diff.comp contDiff_fst
    exact imm_γ₁.diff.comp contDiff_snd

  have cont : Continuous (uncurry normA) := by
    exact (ContDiff.continuous_partial_snd (ϝ_diff) (OrderTop.le_top (1:ℕ∞))).norm


  rcases (unit_compact.prod unit_compact).exists_isMaxOn (unit_nonempty.prod unit_nonempty) cont.continuousOn with
    ⟨⟨s₃, t₃⟩, ⟨s₃in : s₃ ∈ unit, t₃in : t₃ ∈ unit⟩, hst₃⟩
  let K₃ := normA s₃ t₃

  let B := fun s t ↦ (deriv (θ s) t) • (R ((θ s t) + π / 2) * ruffle t) --NOTICE H IS NOT INCLUDED IN THIS STATEMENT.
  let normB := fun s t ↦ ‖B s t‖

  have θ_diff : ContDiff ℝ ⊤ (uncurry θ) := by
    apply ContDiff.add
    apply ContDiff.smul
    apply ContDiff.sub
    exact contDiff_const
    exact ρ_diff.comp contDiff_fst
    exact hθ₀_diff.comp contDiff_snd
    apply ContDiff.smul
    exact ρ_diff.comp contDiff_fst
    exact hθ₁_diff.comp contDiff_snd


  have cont : Continuous (uncurry normB) := by
    have c1 := (ContDiff.continuous_partial_snd (θ_diff) (OrderTop.le_top (1:ℕ∞)))
    have c2 : Continuous (fun (x:(ℝ×ℝ)) ↦ R ((θ x.1 x.2) + π / 2) * ruffle x.2) := by
      apply Continuous.mul
      apply Continuous.comp
      exact Complex.continuous_exp
      apply Continuous.smul
      apply Continuous.add
      exact ContDiff.continuous θ_diff
      exact continuous_const
      exact continuous_const

      rw [duh]
      apply Continuous.add
      apply Continuous.neg
      apply Continuous.comp'
      exact Complex.continuous_sin
      apply Continuous.comp
      exact continuous_mul_left (4 * π : ℂ)
      apply Continuous.comp'
      exact continuous_ofReal
      apply Continuous.comp
      exact continuous_snd
      exact continuous_id'

      apply Continuous.smul
      apply Continuous.comp
      exact continuous_mul_left 2
      apply Continuous.comp'
      exact Complex.continuous_sin
      apply Continuous.comp
      exact continuous_mul_left (2 * π : ℂ)
      apply Continuous.comp'
      exact continuous_ofReal
      exact continuous_snd

      exact continuous_const

    exact (Continuous.smul c1 c2).norm



  rcases (unit_compact.prod unit_compact).exists_isMaxOn (unit_nonempty.prod unit_nonempty) cont.continuousOn with
    ⟨⟨s₂, t₂⟩, ⟨s₂in : s₂ ∈ unit, t₂in : t₂ ∈ unit⟩, hst₂⟩
  let K₂ := normB s₂ t₂

  let C := fun s t ↦ (2 * π) • (deriv ruffle t * R (θ s t)) --NOTICE NEITHER H NOR N IS INCLUDED IN THIS STATEMENT.
  let normC := fun s t ↦ ‖C s t‖

  have cont : Continuous (uncurry normC) := by
    have c1 := ((contDiff_top_iff_deriv.1 (ruffle_diff)).2).continuous

    have c2 : Continuous (uncurry θ) := θ_diff.continuous

    have c3 : Continuous (fun (x:(ℝ×ℝ)) ↦ (2 * π) • (deriv ruffle x.2 * R (θ x.1 x.2))) := by
      apply Continuous.smul
      exact continuous_const
      apply Continuous.mul
      apply Continuous.comp'
      exact c1
      exact continuous_snd
      apply Continuous.comp
      exact Complex.continuous_exp
      apply Continuous.smul
      exact c2
      exact continuous_const

    exact c3.norm


  rcases (unit_compact.prod unit_compact).exists_isMinOn (unit_nonempty.prod unit_nonempty) cont.continuousOn with
    ⟨⟨s₁, t₁⟩, ⟨s₁in : s₁ ∈ unit, t₁in : t₁ ∈ unit⟩, hst₁⟩
  let K₁ := normC s₁ t₁

  have K₁_pos : K₁ > 0 := by
    by_contra opp
    push_neg at opp
    simp only at opp
    have := norm_nonneg ((2 * π) • (deriv ruffle t₁ * R ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁)))
    have opp': ‖(2 * π) • (deriv ruffle t₁ * R ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁))‖ = 0 := by exact LE.le.antisymm opp this
    clear opp this

    rw [norm_smul (2*π) (deriv ruffle t₁ * R ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁))] at opp'
    apply mul_eq_zero.1 at opp'
    rcases opp' with A|opp
    simp at A
    have : π ≠ 0 := by
      exact pi_ne_zero
    exact this A

    rw [norm_mul (deriv ruffle t₁) (R ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁))] at opp
    apply mul_eq_zero.1 at opp
    rcases opp with B|C

    have := ruffle_deriv_neq_zero_on_unit t₁in
    have : ‖deriv ruffle t₁‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr this
    exact this B

    unfold R at C
    have : ∀ t:ℝ, t*I = t• I:= by
      intro t
      simp
    specialize this ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁)
    have final := Complex.norm_exp_ofReal_mul_I ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁)
    rw [this] at final
    rw [final] at C
    linarith


  rcases (root_lemma_maybe K₁ K₂ K₃ K₁_pos H_pos) with ⟨N₀, hN₀⟩

  --Prove K₁ is positive and do the same for H (or set H = 1), get N₀, then N

  let γ : ℝ → ℝ → ℂ := fun s t ↦ ϝ s t + (h s) • (R (θ s t) * ruffle ((N₀+1) * t))
  use γ
  constructor
  --these statements will likely need to be proved out of order, probably starting with the statement of derive_ne
  · have dif : ContDiff ℝ ⊤ (uncurry γ) := by
      have sufficient : ContDiff ℝ ⊤ (fun (x:ℝ × ℝ ) ↦ ϝ x.1 x.2 + (h x.1) • (R (θ x.1 x.2) * ruffle ((N₀+1) * x.2))) := by
        apply ContDiff.add
        exact ϝ_diff
        apply ContDiff.smul
        have := h_diff
        exact ContDiff.fst' this
        apply ContDiff.mul
        apply ContDiff.comp
        exact Complex.contDiff_exp
        apply ContDiff.smul
        exact θ_diff
        exact contDiff_const
        have : ContDiff ℝ ⊤ ( fun (x:ℝ× ℝ) ↦ (↑N₀ + 1) * x.2 ) := by
          apply ContDiff.snd'
          apply ContDiff.mul
          exact contDiff_const
          exact contDiff_id

        have this2 := ruffle_diff
        have fin := ContDiff.comp this2 this
        have duh : (ruffle ∘ fun (x:ℝ× ℝ) ↦ (↑N₀ + 1) * x.2) = (fun (x:ℝ×ℝ) ↦ ruffle ((↑N₀ + 1) * x.2)) := by
          exact rfl

        rw [duh] at fin
        exact fin




      exact sufficient


    have im : ∀ s, CircleImmersion (γ s) := by
      intro s
      have cdiff : ContDiff ℝ ⊤ (γ s) := by
        simp only
        apply ContDiff.add
        apply ContDiff.add
        apply ContDiff.smul
        exact contDiff_const
        exact imm_γ₀.diff
        apply ContDiff.smul
        exact contDiff_const
        exact imm_γ₁.diff
        apply ContDiff.smul
        exact contDiff_const
        apply ContDiff.mul
        apply ContDiff.comp
        exact Complex.contDiff_exp
        apply ContDiff.smul
        apply ContDiff.add
        apply ContDiff.mul
        exact contDiff_const
        exact hθ₀_diff
        apply ContDiff.mul
        exact contDiff_const
        exact hθ₁_diff
        exact contDiff_const

        have : ContDiff ℝ ⊤ ( fun (x:ℝ) ↦ (↑N₀ + 1) * x ) := by
          apply ContDiff.mul
          exact contDiff_const
          exact contDiff_id

        have this2 := ruffle_diff

        have fin := ContDiff.comp this2 this

        have duh : (ruffle ∘ fun (x:ℝ) ↦ (↑N₀ + 1) * x) = (fun (x:ℝ) ↦ ruffle ((↑N₀ + 1) * x)) := by
          exact rfl

        rw [duh] at fin
        exact fin


      have periodic : Periodic (γ s) 1 := by
        unfold Periodic
        intro x

        have pϝ : Periodic (ϝ s) 1 := by
          intro x
          simp
          have pγ₀ := imm_γ₀.per x
          have pγ₁ := imm_γ₁.per x
          rw [pγ₀]
          rw [pγ₁]

        have pθ : Periodic (θ s) 1 := by
          intro x
          simp
          rw [hθ₀_per x]
          rw [hθ₁_per x]


        have p_ruffle : Periodic (fun x ↦ ruffle ((N₀ + 1) * x)) 1 := by
          intro x
          simp
          unfold ruffle
          simp
          constructor
          have : Real.sin (4 * π * ((↑N₀ + 1) * (x + 1))) = Real.sin (4 * π * ((↑N₀ + 1) * x ) + 4 * π * (N₀ + 1)) := by
            ring_nf

          rw [this]

          have : ∀ k: ℕ, Real.sin (4 * π * (k * x ) + 4 * π * k) = Real.sin (4 * π * (k * x )) := by
            intro k
            have fact := Real.sin_periodic
            have fact2 := Function.Periodic.nat_mul fact (2*k)
            specialize fact2 (4 * π * (↑k * x))
            simp at fact2
            have : 2 * ↑k * (2 * π) = 4 * π * k := by
              ring
            rw [this] at fact2
            rw [fact2]
          specialize this (N₀ +1)
          push_cast at this

          rw [this]

          have : Real.sin (2 * π * ((↑N₀ + 1) * (x + 1))) = Real.sin (2 * π * ((↑N₀ + 1) * x ) + 2 * π * (N₀ + 1)) := by
            ring_nf

          rw [this]

          have : ∀ k: ℕ, Real.sin (2 * π * (k * x ) + 2 * π * k) = Real.sin (2 * π * (k * x )) := by
            intro k
            have fact := Real.sin_periodic
            have fact2 := Function.Periodic.nat_mul fact (k)
            specialize fact2 (2 * π * (↑k * x))

            rw [← fact2]

            have : ↑k * (2 * π) = 2 * π * ↑k := by
              ring
            rw [this]

          specialize this (N₀ +1)
          push_cast at this

          rw [this]

        simp
        specialize pϝ x
        specialize pθ x
        specialize p_ruffle x
        simp at pϝ
        rw [← pϝ]
        simp

        simp at pθ
        rw [← pθ]
        simp

        simp at p_ruffle
        rw [←p_ruffle ]
        simp





      have dγnon0 : ∀ t, deriv (γ s) t ≠ 0 := by sorry
      exact { diff := cdiff, per := periodic, deriv_ne := dγnon0 }

    exact { diff := dif, imm := im }
  --HtpyCircleImmersion (γ : ℝ → ℝ → ℂ)
    --requires diff : ContDiff ℝ ⊤ (uncurry γ)
      --should fall out of some composition stuff
    -- requires imm : ∀ s, CircleImmersion (γ s)
      --requires diff : ContDiff ℝ ⊤ (γ s)
      --requires per : Periodic (γ s) 1
        --requires ∀ t, (γ s) (t + 1) = (γ s) t
          --(ϝ s) := fun t ↦ t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
          --(θ s) := t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
          --(γ s) := fun t ↦ (ϝ s) t + (h s) * (R ((θ s) t)) * ruffling (N * t)
          --       = fun t ↦ (fun t ↦ t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t) t + (h s) * (R ((t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t) t)) * ruffle (N * t)
          --       = ...
      --requires derive_ne : ∀ t, deriv γ t ≠ 0
        --big thing here
        --for a given s, K₁ = min of the norm of the thing with h and N in it
          --exists cuz norm has clear lower bound 0, show that this in particular is nonzero because the terms are nonnegative and are never simultaneously zero
        --for a given s, K₂ = max(‖h * deriv (θ s) * R * ruffle‖) on s, t ∈ [0, 1]
          --exists since everything is bounded
        --for a given s, K₃ = max(‖(1 - ρ s) * (γ₀ t) + (ρ s) * (γ₁ t)‖) on s, t ∈ [0, 1]
          --exists since (ρ s) and γ₀ and γ₁ are all bounded on the period, etc or whatever
        --using root_lemma_maybe (or whatever it renamed to), get N₀ and define γ, carry out some triangle inequality argument showing that ∀ s, ‖deriv (γ s) t‖ > 0, and hence nonzero.
  · constructor
    · intro t
      simp [γ, ϝ]
    · intro t
      simp [γ, ϝ]

end WhitneyGraustein
