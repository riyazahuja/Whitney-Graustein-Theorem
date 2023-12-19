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


axiom CircleImmersion.lift {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) : ℝ → ℝ

variable {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ)

axiom CircleImmersion.contDiff_lift : ContDiff ℝ ⊤ imm_γ.lift

axiom CircleImmersion.deriv_eq (t : ℝ) : deriv γ t = ‖deriv γ t‖ * Complex.exp (I * imm_γ.lift t)

axiom CircleImmersion.turningNumber {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) : ℤ

axiom CircleImmersion.lift_add (t : ℝ) (k : ℤ) : imm_γ.lift (t + k) = imm_γ.lift t + k*imm_γ.turningNumber*2*π

lemma CircleImmersion.lift_add_one (t : ℝ) : imm_γ.lift (t + 1) = imm_γ.lift t + imm_γ.turningNumber*2*π := by
  simpa using imm_γ.lift_add t 1

structure HtpyCircleImmersion (γ : ℝ → ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ (uncurry γ)
  imm : ∀ s, CircleImmersion (γ s)

/-
∀K₁, K₂, K₃ : ℝ, with K₁ > 0, and ∀H > 0, we claim that  there exists some N₀ such that N ≥ N₀
implies that K₁HN - K₂H - K₃ > 0

This is required to construct our gamma function and for the main phase.
-/

lemma root_lemma_maybe {H : ℝ} (K₁ : ℝ) (K₂ : ℝ) (K₃ : ℝ) (K₁_pos : K₁ > 0) (H_pos : H > 0) : ∃ (N₀ : ℕ), ∀ N > N₀, (K₁ * H) * N - (K₂ * H + K₃) > 0 := by
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

section phases

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

lemma unit_compact : IsCompact unit := isCompact_Icc
lemma unit_nonempty : Set.Nonempty unit := nonempty_of_nonempty_subtype

end phases



section triangle_inequalities

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

end triangle_inequalities





section coer_properties


lemma coer_deriv : ∀ t:ℝ, deriv (fun (x:ℝ) ↦ (x:ℂ)) t = 1 := by
  intro t
  have id_deriv : HasDerivAt (fun (x:ℂ)↦ (x:ℂ)) 1 t := by exact hasDerivAt_id' ((↑t):ℂ)
  have hda_main := HasDerivAt.comp_ofReal id_deriv
  exact HasDerivAt.deriv hda_main


/-Credit: Kevin Buzzard-/
lemma coer_diff : ContDiff ℝ ⊤ fun (x:ℝ) ↦ (x:ℂ) :=
  ContinuousLinearMap.contDiff ofRealClm

end coer_properties





section H

def H : ℝ := 1

lemma H_pos : 0 < H := Real.zero_lt_one

def h : ℝ → ℝ := sorry

lemma h_diff : ContDiff ℝ ⊤ h  := sorry

lemma h_main : ∀ᶠ (x : ℝ) in 𝓝ˢ main, h x = 0 := sorry

lemma h_antimain : ∀ᶠ (x : ℝ) in 𝓝ˢ antimain, h x = H := sorry

lemma h_mem : ∀ (x : ℝ), h x ∈ Icc 0 1 := sorry

@[simp] lemma h_zero : h 0 = 0 := sorry

@[simp] lemma h_one : h 1 = 0 := sorry

end H





section ruffle

variable (N:ℕ)

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


-- Also check `deriv.scomp`
lemma ruffle_deriv_neq_zero_on_unit{t:ℝ}(ht: t ∈ unit): deriv ruffle t ≠ 0 := by
  rw[duh]

  intro opp

  rw [deriv_add] at opp
  rw [deriv.neg] at opp

  have : (fun (x:ℝ) ↦ ↑(Real.sin (4 * π * x))) = (fun (x:ℝ)↦ (x:ℂ)) ∘ (fun (y:ℝ) ↦ Real.sin (4 * π * y)) := by exact rfl
  rw [this] at opp
  clear this

  /- rw [deriv.comp] at opp


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

  have : (fun (x:ℝ) ↦ Complex.sin (2 * ↑π * ↑x)) = Complex.sin ∘ (fun (x:ℝ) ↦ (2 * ↑π * ↑x)) := by exact rfl
  rw [this] at opp
  rw [deriv.comp] at opp
  rw [Complex.deriv_sin] at opp
  clear this
  rw [deriv_mul] at opp
  rw [deriv_const, zero_mul, zero_add] at opp
  rw [coer_deriv t, mul_one] at opp
  sorry


  sorry
  sorry
  sorry
  sorry -/
  sorry
  sorry
  sorry


  /-TODO!!!!!! -/




lemma ruffle_diff : ContDiff ℝ ⊤ ruffle := by

  rw [duh]
  apply ContDiff.add
  apply ContDiff.neg
  -- This statements make the composition explicit so ContDiff.comp can work
  have : (fun x ↦ ↑(Real.sin (4 * π * x))) = (fun (y:ℝ) ↦(y:ℂ)) ∘ (fun x ↦ Real.sin (4 * π * x)) := by
    exact rfl
  rw [this]
  apply ContDiff.comp
  exact coer_diff

  --same as previous
  have : (fun x ↦ Real.sin (4 * π * x) )= Real.sin ∘ (fun x ↦ (4 * π * x)) := by
    exact rfl
  rw[this]
  apply ContDiff.comp
  exact Real.contDiff_sin
  apply ContDiff.mul
  exact contDiff_const
  exact contDiff_id


  apply ContDiff.smul
  apply ContDiff.mul
  exact contDiff_const
  --same as previous
  have : (fun x ↦ Real.sin (2 * π * x) )= Real.sin ∘ (fun x ↦ (2 * π * x)) := by
    exact rfl
  rw[this]

  apply ContDiff.comp
  exact Real.contDiff_sin
  apply ContDiff.mul
  exact contDiff_const
  exact contDiff_id

  exact contDiff_const



lemma p_ruffle : Periodic (fun x ↦ ruffle (N * x)) 1 := by
          intro x
          simp
          unfold ruffle
          simp
          constructor
          have : Real.sin (4 * π * (N * (x + 1))) = Real.sin (4 * π * (N * x ) + 4 * π * N) := by
            ring_nf

          rw [this]

          have : ∀ k: ℕ, Real.sin (4 * π * (k * x ) + 4 * π * k) = Real.sin (4 * π * (k * x )) := by
            intro k
            have fact2 := Function.Periodic.nat_mul Real.sin_periodic (2*k)
            specialize fact2 (4 * π * (↑k * x))
            simp at fact2
            have : 2 * ↑k * (2 * π) = 4 * π * k := by ring
            rw [this] at fact2
            rw [fact2]
          specialize this N
          push_cast at this

          rw [this]

          have : Real.sin (2 * π * (N * (x + 1))) = Real.sin (2 * π * (N * x) + 2 * π * N) := by
            ring_nf

          rw [this]

          have : ∀ k : ℕ, Real.sin (2 * π * (k * x) + 2 * π * k) = Real.sin (2 * π * (k * x)) := by
            intro k
            have fact := Real.sin_periodic
            have fact2 := Function.Periodic.nat_mul fact (k)
            specialize fact2 (2 * π * (↑k * x))

            rw [← fact2]

            have : ↑k * (2 * π) = 2 * π * ↑k := by
              ring
            rw [this]

          specialize this N
          push_cast at this

          rw [this]

end ruffle




section ρ

-- See https://github.com/leanprover-community/sphere-eversion/blob/master/SphereEversion/ToMathlib/Analysis/CutOff.lean
def ρ : ℝ → ℝ := sorry

lemma ρ_diff : ContDiff ℝ ⊤ ρ := sorry

lemma ρ_ruffling : EqOn ρ 0 ruffling := sorry

lemma ρ_unruffling : EqOn ρ 1 unruffling := sorry

lemma ρ_mem : ∀ x, ρ x ∈ Icc (0 : ℝ) 1 := sorry

@[simp] lemma rho_zero : ρ 0 = 0 := sorry

@[simp] lemma rho_one : ρ 1 = 1 := sorry


end ρ




/-- A pair of circle immersion satisfiying the assumption of Whitney-Graustein. -/
structure WG_pair where
  γ₀ : ℝ → ℂ
  γ₁ : ℝ → ℂ
  imm_γ₀ : CircleImmersion γ₀
  imm_γ₁ : CircleImmersion γ₁
  turning_eq : imm_γ₀.turningNumber = imm_γ₁.turningNumber



section ϝ
variable (p : WG_pair)

@[pp_dot]
def WG_pair.ϝ (s t : ℝ) := (1 - (ρ s)) • (p.γ₀ t) + (ρ s) • p.γ₁ t

@[simp]
lemma WG_pair.ϝ_apply (s t : ℝ) : p.ϝ s t = (1 - (ρ s)) • (p.γ₀ t) + (ρ s) • p.γ₁ t := rfl

lemma WG_pair.ϝ_diff : ContDiff ℝ ⊤ (uncurry p.ϝ) := by
  apply ContDiff.add
  apply ContDiff.smul
  apply ContDiff.sub
  exact contDiff_const
  exact ρ_diff.comp contDiff_fst
  exact p.imm_γ₀.diff.comp contDiff_snd
  apply ContDiff.smul
  exact ρ_diff.comp contDiff_fst
  exact p.imm_γ₁.diff.comp contDiff_snd

lemma cont_norm_ϝ : Continuous (uncurry (fun s t ↦ ‖deriv (p.ϝ s) t‖)) :=
  (ContDiff.continuous_partial_snd p.ϝ_diff le_top).norm

lemma pϝ : ∀s, Periodic (p.ϝ s) 1 := by
          intro s x
          unfold WG_pair.ϝ
          have pγ₀ := p.imm_γ₀.per x
          have pγ₁ := p.imm_γ₁.per x
          rw [pγ₀]
          rw [pγ₁]

end ϝ




section θ

variable (p : WG_pair)

@[pp_dot]
def WG_pair.θ₀ := p.imm_γ₀.lift

@[pp_dot]
def WG_pair.θ₁ := p.imm_γ₁.lift

@[pp_dot]
def WG_pair.θ (s t : ℝ) := (1 - (ρ s)) * (p.θ₀ t) + (ρ s) * (p.θ₁ t)

@[simp]
lemma WG_pair.θ_mk {γ₀ γ₁} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁) (turning_eq : imm_γ₀.turningNumber = imm_γ₁.turningNumber) (s t) :
  (⟨γ₀, γ₁, imm_γ₀, imm_γ₁, turning_eq⟩ : WG_pair).θ s t = (1 - (ρ s)) * (imm_γ₀.lift t) + (ρ s) * (imm_γ₁.lift t) := rfl

lemma WG_pair.θ_diff : ContDiff ℝ ⊤ (uncurry p.θ) := by
  apply ContDiff.add
  apply ContDiff.smul
  apply ContDiff.sub
  exact contDiff_const
  exact ρ_diff.comp contDiff_fst
  exact p.imm_γ₀.contDiff_lift.comp contDiff_snd
  apply ContDiff.smul
  exact ρ_diff.comp contDiff_fst
  exact p.imm_γ₁.contDiff_lift.comp contDiff_snd

--def B (s t : ℝ) := (deriv (p.θ s) t) • (R ((p.θ s t) + π / 2) * ruffle t)

end θ



section R


def R : ℝ → ℂ := fun θ ↦ cexp (θ • I)

lemma dR {p:WG_pair} (s t : ℝ) : deriv (fun (t' : ℝ) ↦ R (p.θ s t')) t = R ((p.θ s t) + π / 2) * deriv (p.θ s) t := by sorry


lemma p_R : Periodic R (2*π) := by
          intro x
          unfold R
          have := Complex.exp_periodic (x• I)
          rw [← this]
          simp
          have : (↑x + 2 * ↑π) * I = ↑x * I + 2 * ↑π * I := by
            ring
          rw [this]


end R




section ABC

variable (p : WG_pair)

namespace WG_pair
section A

def A := fun s t ↦ deriv (p.ϝ s) t
def normA := fun s t ↦ ‖(A p) s t‖

lemma contA : Continuous (uncurry (normA p)) := (ContDiff.continuous_partial_snd (p.ϝ_diff) (OrderTop.le_top (1:ℕ∞))).norm

end A



section B

def B (s t : ℝ) := (deriv (p.θ s) t) • (R ((p.θ s t) + π / 2) * ruffle t)
def normB := fun s t ↦ ‖(B p) s t‖



lemma contB : Continuous (uncurry (normB p)) := by
  have c1 := (ContDiff.continuous_partial_snd (p.θ_diff) (OrderTop.le_top (1:ℕ∞)))
  have c2 : Continuous (fun (x:(ℝ×ℝ)) ↦ R ((p.θ x.1 x.2) + π / 2) * ruffle x.2) := by
    apply Continuous.mul
    apply Continuous.comp
    exact Complex.continuous_exp
    apply Continuous.smul
    apply Continuous.add
    exact ContDiff.continuous p.θ_diff
    exact continuous_const
    exact continuous_const

    rw [duh]
    apply Continuous.add
    apply Continuous.neg
    apply Continuous.comp'
    exact continuous_ofReal
    apply Continuous.comp'
    exact Real.continuous_sin
    apply Continuous.comp
    exact continuous_mul_left (4 * π : ℝ)
    apply Continuous.comp'
    exact continuous_snd
    exact continuous_id'

    apply Continuous.smul
    apply Continuous.comp
    exact continuous_mul_left 2
    apply Continuous.comp'
    exact Real.continuous_sin
    apply Continuous.comp
    exact continuous_mul_left (2 * π : ℝ)
    apply Continuous.comp'
    exact continuous_snd

    exact continuous_id'

    exact continuous_const

  exact (Continuous.smul c1 c2).norm

end B


section C

def C := fun s t ↦ (2 * π) • (deriv ruffle t * R (p.θ s t)) --NOTICE NEITHER H NOR N₀ IS INCLUDED IN THIS STATEMENT.
def normC := fun s t ↦ ‖p.C s t‖--Im not quite sure how to address this; the underlying argument is that this is true for any nonzero scaling of the t argued to the deriv, and similarly the extrema of ‖C‖ are also unchanged.

lemma contC : Continuous (uncurry p.normC) := by
  have c1 := ((contDiff_top_iff_deriv.1 (ruffle_diff)).2).continuous

  have c2 : Continuous (uncurry p.θ) := p.θ_diff.continuous

  have c3 : Continuous (fun (x:(ℝ×ℝ)) ↦ (2 * π) • (deriv ruffle x.2 * R (p.θ x.1 x.2))) := by
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


end C

section K₁

lemma exists_min_C : ∃ x ∈ unit ×ˢ unit, IsMinOn (uncurry (normC p)) (unit ×ˢ unit) x :=
  (unit_compact.prod unit_compact).exists_isMinOn (unit_nonempty.prod unit_nonempty) p.contC.continuousOn

@[pp_dot]
def t₁ := p.exists_min_C.choose.1

@[pp_dot]
def s₁ := p.exists_min_C.choose.2

@[pp_dot]
def K₁ := ‖p.C p.s₁ p.t₁‖

lemma K₁_pos : p.K₁ > 0 := by
  by_contra opp
  push_neg at opp
  let t₁ := p.t₁
  let s₁ := p.s₁
  let θ₀ := p.θ₀
  let θ₁ := p.θ₁

  simp only [WG_pair.K₁, WG_pair.C] at opp
  have := norm_nonneg ((2 * π) • (deriv ruffle t₁ * R ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁)))
  have opp': ‖(2 * π) • (deriv ruffle t₁ * R ((1 - ρ s₁) * θ₀ t₁ + ρ s₁ * θ₁ t₁))‖ = 0 := by
    exact opp.antisymm this
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

  have := ruffle_deriv_neq_zero_on_unit p.exists_min_C.choose_spec.1.1
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

end K₁


end WG_pair

end ABC




section WGMain


theorem whitney_graustein {γ₀ γ₁ : ℝ → ℂ} {t : ℝ} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁) :
  (imm_γ₀.turningNumber = imm_γ₁.turningNumber) → ∃ (γ : ℝ → ℝ → ℂ), HtpyCircleImmersion γ ∧ ((∀ t, γ 0 t = γ₀ t) ∧ (∀ t, γ 1 t = γ₁ t)) := by
  intro hyp --we want to show that since there exists some N,H pair such that... then there exists...
  let tn := CircleImmersion.turningNumber imm_γ₀

  let p : WG_pair := ⟨γ₀, γ₁, imm_γ₀, imm_γ₁, hyp⟩
  let θ := p.θ
  let θ₀ := p.θ₀
  let θ₁ := p.θ₁

  rcases (unit_compact.prod unit_compact).exists_isMaxOn (unit_nonempty.prod unit_nonempty) p.contA.continuousOn with
    ⟨⟨s₃, t₃⟩, ⟨s₃in : s₃ ∈ unit, t₃in : t₃ ∈ unit⟩, hst₃⟩
  let K₃ := p.normA s₃ t₃

  rcases (unit_compact.prod unit_compact).exists_isMaxOn (unit_nonempty.prod unit_nonempty) p.contB.continuousOn with
    ⟨⟨s₂, t₂⟩, ⟨s₂in : s₂ ∈ unit, t₂in : t₂ ∈ unit⟩, hst₂⟩
  let K₂ := p.normB s₂ t₂


  rcases (unit_compact.prod unit_compact).exists_isMinOn (unit_nonempty.prod unit_nonempty) p.contC.continuousOn with
    ⟨⟨s₁, t₁⟩, ⟨s₁in : s₁ ∈ unit, t₁in : t₁ ∈ unit⟩, hst₁⟩
  let K₁ := p.K₁

  have K₁_pos : K₁ > 0 := p.K₁_pos

  rcases (root_lemma_maybe K₁ K₂ K₃ K₁_pos H_pos) with ⟨N₀, hN₀⟩

  --Prove K₁ is positive and do the same for H (or set H = 1), get N₀, then N

  let γ : ℝ → ℝ → ℂ := fun s t ↦ p.ϝ s t + (h s) • (R (p.θ s t) * ruffle ((N₀ + 1) * t))
  use γ
  constructor
  --these statements will likely need to be proved out of order, probably starting with the statement of derive_ne
  · have dif : ContDiff ℝ ⊤ (uncurry γ) := by
      have sufficient : ContDiff ℝ ⊤ (fun (x : ℝ × ℝ) ↦ p.ϝ x.1 x.2 + (h x.1) • (R (p.θ x.1 x.2) * ruffle ((N₀ + 1) * x.2))) := by
        apply ContDiff.add
        exact p.ϝ_diff
        apply ContDiff.smul
        exact ContDiff.fst' h_diff
        apply ContDiff.mul
        apply ContDiff.comp
        exact Complex.contDiff_exp
        apply ContDiff.smul
        exact p.θ_diff
        exact contDiff_const
        have : ContDiff ℝ ⊤ (fun (x : ℝ × ℝ) ↦ (↑N₀ + 1) * x.2) := by
          apply ContDiff.snd'
          apply ContDiff.mul
          exact contDiff_const
          exact contDiff_id
        have this2 := ruffle_diff
        have fin := ContDiff.comp this2 this
        have duh : (ruffle ∘ fun (x : ℝ × ℝ) ↦ (↑N₀ + 1) * x.2) = (fun (x : ℝ × ℝ) ↦ ruffle ((↑N₀ + 1) * x.2)) := by
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
        exact p.imm_γ₀.contDiff_lift
        apply ContDiff.mul
        exact contDiff_const
        exact p.imm_γ₁.contDiff_lift
        exact contDiff_const

        have : ContDiff ℝ ⊤ (fun (x : ℝ) ↦ (↑N₀ + 1) * x) := ContDiff.mul contDiff_const contDiff_id

        have fin := ContDiff.comp ruffle_diff this

        have duh : (ruffle ∘ fun (x : ℝ) ↦ (↑N₀ + 1) * x) = (fun (x : ℝ) ↦ ruffle ((↑N₀ + 1) * x)) := rfl

        rw [duh] at fin
        exact fin


      have periodic : Periodic (γ s) 1 := by

      /-REDO, θ IS NOT PERIODIC!!!!

      -/
        sorry
/-         unfold Periodic
        intro x
        dsimp only [γ]


        rw [pϝ p s x]
        have := p_ruffle (↑N₀+1) x
        simp at this
        rw [this]

        clear this

        have : R (p.θ s x) = R (p.θ s (x+1)) := by
          unfold WG_pair.θ
          have t0 := imm_γ₀.lift_add x 1
          have t1 := imm_γ₁.lift_add x 1

          have eq0: p.θ₀ = CircleImmersion.lift imm_γ₀ := by
            exact rfl

          have eq1: p.θ₁ = CircleImmersion.lift imm_γ₁ := by
            exact rfl

          rw [eq0, eq1]
          simp at t0
          simp at t1

          rw [t0,t1]
          rw [hyp]

          have := (Function.Periodic.int_mul p_R (tn)) ((1 - ρ s) * CircleImmersion.lift imm_γ₀ x + ρ s * CircleImmersion.lift imm_γ₁ x)
          rw[← this]

          have : (1 - ρ s) * CircleImmersion.lift imm_γ₀ x + ρ s * CircleImmersion.lift imm_γ₁ x + ↑tn * (2 * π) = (1 - ρ s) * (CircleImmersion.lift imm_γ₀ x + ↑(CircleImmersion.turningNumber imm_γ₁) * 2 * π) + ρ s * (CircleImmersion.lift imm_γ₁ x + ↑(CircleImmersion.turningNumber imm_γ₁) * 2 * π) := by
            ring_nf
            simp
            rw [hyp]
            rw [mul_comm]
          rw [this]


        rw [← this]




        simp at p_R
        have := Function.Periodic.int_mul p_R (tn)



        rw [← pθ]
        simp

        simp at p_ruffle
        rw [← p_ruffle]
        simp -/

      have dγnon0 : ∀ t, deriv (γ s) t ≠ 0 := by
        intro t
        --gotta split this up by phase, just assume this is the "main phase" proof for now where h s = H for all s
        have subcritical : K₁ * H * ↑(N₀ + 1) - (K₂ * H + K₃) > 0 := hN₀ (N₀ + 1) (Nat.lt.base N₀) --just so youre aware
        have critical : ‖deriv (γ s) t‖ ≥ K₁ * (N₀ + 1) * H - K₂ * H - K₃ := sorry --we need this


        have bro_on_god₀ : deriv (fun t' ↦ (R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t') * ruffle ((↑N₀ + 1) * t'))) t = _ := by
          calc
          deriv (fun t' ↦ (R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t') * ruffle ((↑N₀ + 1) * t'))) t
            = (fun t' ↦ R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t')) t * deriv (fun t' ↦ ruffle ((↑N₀ + 1) * t')) t + deriv (fun t' ↦ R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t')) t * (fun t' ↦ ruffle ((↑N₀ + 1) * t')) t := by
              rw [deriv_mul]
              exact
                add_comm
                  (deriv (fun t' ↦ R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t')) t * ruffle ((↑N₀ + 1) * t))
                  (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * deriv (fun t' ↦ ruffle ((↑N₀ + 1) * t')) t)

              have d_θ: Differentiable ℝ (p.θ s) := by
                simp only
                apply Differentiable.add
                apply Differentiable.mul
                exact differentiable_const (1 - ρ s)
                have := p.imm_γ₀.contDiff_lift.differentiable (OrderTop.le_top (1:ℕ∞))
                exact this
                apply Differentiable.mul
                exact differentiable_const (ρ s)
                have this2 := p.imm_γ₁.contDiff_lift.differentiable (OrderTop.le_top (1:ℕ∞))
                exact this2
              --have := dR s t

              have : HasDerivAt ((fun t' ↦ R (p.θ s t'))) (R (p.θ s t + π / 2) * ↑(deriv (p.θ s) t)) t := by
                sorry -- HOW TO CONVERT DERIV TO HASDERIVAT????

              exact HasDerivAt.differentiableAt this

              have rewrite : (fun t' ↦ ruffle ((↑N₀ + 1) * t')) = ruffle ∘ (fun t' ↦ (↑N₀ + 1) * t') := by
                exact rfl
              rw [rewrite]
              apply DifferentiableAt.comp
              have d_ruff : Differentiable ℝ ruffle := (ruffle_diff.differentiable (OrderTop.le_top (1:ℕ∞)))
              exact Differentiable.differentiableAt d_ruff
              apply DifferentiableAt.mul

              simp
              simp

          _ = (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t)) * (↑N₀ + 1)) + ((R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t + π / 2) * deriv (p.θ s) t) * ruffle ((↑N₀ + 1) * t)) := by --left term is an rfl and a chain rule, right term using dR (up to a hidden rfl and rewriting the statement of dR)



            have fact1 : deriv (fun t' ↦ ruffle ((↑N₀ + 1) * t')) t = deriv ruffle ((↑N₀ + 1) * t) * (↑N₀ + 1) := by
              have : (fun t' ↦ ruffle ((↑N₀ + 1) * t')) = ruffle ∘ (fun t' ↦ ((↑N₀+1)* t' ) ) := by exact rfl
              rw[this]
              have h1 : DifferentiableAt ℝ ruffle ((N₀ + 1) * t) := by sorry

              have h2 : DifferentiableAt ℝ (fun (t':ℝ) ↦ (N₀ + 1) * t') t := by sorry

              sorry





            have fact2 : deriv (fun t' ↦ R ((1 - ρ s) * θ₀ t' + ρ s * θ₁ t')) t = R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * ↑(deriv (fun t ↦ (1 - ρ s) * θ₀ t + ρ s * θ₁ t) t) := by
              exact dR s t



            rw[fact1,fact2]
            congr 1
            ring













          --the norms of each of the above terms are (supposedly) bounded by K₁ and K₂ respectively. Might need to demonstrate that these terms are identical to the things in those statements
        have bro_on_god₁ : deriv (γ s) t = (((1 - ↑(ρ s)) * deriv γ₀ t) + (↑(ρ s) * deriv γ₁ t)) + ↑(h s) * (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t)) * (↑N₀ + 1)) + ↑(h s) * ((R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t + π / 2) * deriv (p.θ s) t) * ruffle ((↑N₀ + 1) * t)) := by
          calc
          deriv (γ s) t = deriv (fun t' ↦ p.ϝ s t' + (h s) • (R (θ s t') * ruffle ((N₀ + 1) * t'))) t := rfl
          _ = deriv (fun t' ↦ (1 - ↑(ρ s)) * γ₀ t') t + deriv (fun t' ↦ ↑(ρ s) * γ₁ t') t + deriv (fun t' ↦ ↑(h s) * (R ((1 - ρ s) * θ₀ t' + ρ s * θ₁ t') * ruffle ((↑N₀ + 1) * t'))) t := by --rw deriv_add _ _ twice i think or rw with linearity to cover several lines if thats a thing we can do
              rw [deriv_add]
              simp (config := {zeta := false})
              rw [deriv_add]
              simp (config := {zeta := false})
              rfl
              all_goals sorry


          _ = ((1 - ↑(ρ s)) * deriv (fun t' ↦ γ₀ t') t) + (↑(ρ s) * deriv (fun t' ↦ γ₁ t') t) + (↑(h s) * deriv (fun t' ↦ (R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t') * ruffle ((↑N₀ + 1) * t'))) t) := by --pulling out a complex constant thrice
              rw [deriv_mul]
              rw [deriv_const, zero_mul, zero_add]
              rw [deriv_mul]
              rw [deriv_const, zero_mul, zero_add]
              rw [deriv_mul]
              rw [deriv_const, zero_mul, zero_add]


              /-
              SAME DIFFERENITABLEAT THINGS AS BEFORE
              -/
              sorry
              sorry
              sorry
              sorry
              sorry
              sorry


          _ = (((1 - ↑(ρ s)) * deriv γ₀ t) + (↑(ρ s) * deriv γ₁ t)) + (↑(h s) * deriv (fun t' ↦ (R ((1 - ρ s) * p.θ₀ t' + ρ s * p.θ₁ t') * ruffle ((↑N₀ + 1) * t'))) t) := by--associating A
              exact rfl

          _ = (((1 - ↑(ρ s)) * deriv γ₀ t) + (↑(ρ s) * deriv γ₁ t)) + ↑(h s) * (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t)) * (↑N₀ + 1)) + ↑(h s) * ((R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t + π / 2) * deriv (p.θ s) t) * ruffle ((↑N₀ + 1) * t)) := by--using the identity from bro_on_god₀
              rw[bro_on_god₀]

              simp
              sorry




        /-
        have ff : ‖((1 - ↑(ρ s)) * deriv γ₀ t + ↑(ρ s) * deriv γ₁ t) + ↑(h s) * (R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t) * ruffle ((↑N₀ + 1) * t) + ↑(h s) * R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * deriv ruffle ((↑N₀ + 1) * t) * (↑N₀ + 1)‖ > 0 := by
          calc--oh RIP I think I have to write this backwards (so that H shows up on both terms rather than just one)
          ‖((1 - ↑(ρ s)) * deriv γ₀ t + ↑(ρ s) * deriv γ₁ t) + ↑(h s) * (R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t) * ruffle ((↑N₀ + 1) * t) + ↑(h s) * R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * deriv ruffle ((↑N₀ + 1) * t) * (↑N₀ + 1)‖
            ≥ ‖↑(h s) * R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t)) * (↑N₀ + 1)‖ - ‖↑(h s) * (R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t) * ruffle ((↑N₀ + 1) * t)‖ - ‖(1 - ↑(ρ s)) * deriv γ₀ t + ↑(ρ s) * deriv γ₁ t‖ := in_particular
          _ = ‖↑(h s) * R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t)) * (↑N₀ + 1)‖ - ‖↑(h s) * (R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t) * ruffle ((↑N₀ + 1) * t)‖ - ‖↑(deriv (ϝ s) t)‖ := sorry --by rw [dϝ s t] + a few coercion things on the last term
          _ ≥ ‖↑(h s) * R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t)) * (↑N₀ + 1)‖ - ‖↑(h s) * (R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t) * ruffle ((↑N₀ + 1) * t)‖ - K₃ := sorry --im not sure if weve addressed how to require the computation is true on the unit, but in this case it really is totally bounded
          _ = ‖↑(h s)‖ * ‖((↑N₀ : ℂ) + 1)‖ * ‖R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t))‖ - ‖↑(h s)‖ * ‖R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t * ruffle ((↑N₀ + 1) * t)‖ - K₃ := sorry --splitting along multiplications of h and n components
          _ = H * (↑N₀ + 1 : ℝ) * ‖R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t) * (deriv ruffle ((↑N₀ + 1) * t))‖ - H * ‖R ((1 - ρ s) * θ₀ t + ρ s * θ₁ t + π / 2) * deriv (θ s) t * ruffle ((↑N₀ + 1) * t)‖ - K₃ := sorry --addressing ‖((↑N₀ : ℂ) + 1)‖ and h s in the main phase
          _ ≥ H * (↑N₀ + 1 : ℝ) * K₃ - H * K₂ - K₃ := sorry --the boundings
          _ > 0 := sorry --rearrange subcritical
          -/

        have ff : ‖(1 - ↑(ρ s)) * deriv γ₀ t + ↑(ρ s) * deriv γ₁ t + ↑(h s) * (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * deriv ruffle ((↑N₀ + 1) * t) * (↑N₀ + 1)) + ↑(h s) * (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t + π / 2) * ↑(deriv (p.θ s) t) * ruffle ((↑N₀ + 1) * t))‖ > 0 := by
          let N:ℕ := (N₀) +1
          let A := (1 - ↑(ρ s)) * deriv γ₀ t + ↑(ρ s) * deriv γ₁ t
          let B := ↑(h s) * R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t + π / 2) * ↑(deriv (p.θ s) t) * ruffle (N * t)
          let C := ↑(h s) * R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * deriv ruffle (N * t) * N


          calc
          ‖(1 - ↑(ρ s)) * deriv γ₀ t + ↑(ρ s) * deriv γ₁ t + ↑(h s) * (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t) * deriv ruffle ((↑N₀ + 1) * t) * (↑N₀ + 1)) + ↑(h s) * (R ((1 - ρ s) * p.θ₀ t + ρ s * p.θ₁ t + π / 2) * ↑(deriv (p.θ s) t) * ruffle ((↑N₀ + 1) * t))‖
            = ‖A+B+C‖  := by sorry
          _ ≥ ‖C‖-‖B‖-‖A‖ := in_particular
          _ ≥ H * N * K₁ - H * K₂ - K₃ := by sorry
          _ > 0 := by
            have : N > N₀ := by simp
            have := hN₀ N (this)
            have duh : K₁ * H * ↑N - (K₂ * H + K₃) = H * ↑N * K₁ - H * K₂ - K₃ := by
              ring
            rw [← duh]
            exact this







        have f : ‖deriv (γ s) t‖ > 0 := by
          rw [bro_on_god₁]
          exact ff

        exact ne_zero_of_map (ne_of_gt f)

        --expanding in preparation for a rewrite
        --then develop the facts that the norm of each term is appropriately related to each K
        --then below apply the rewrites, triangle inequality, bing bang boom you gottem
        --also you might need a little commutativity/associativity inside the norm to translate between facts here

      exact { diff := cdiff, per := periodic, deriv_ne := dγnon0 }

    exact { diff := dif, imm := im }

  · constructor
    · intro t
      simp [γ]
    · intro t
      simp [γ]


end WGMain
end WhitneyGraustein
--apparently there is an unterminated comment somewhere; I searched briefly, could not find.
