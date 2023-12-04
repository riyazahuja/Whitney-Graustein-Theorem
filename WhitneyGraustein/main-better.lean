import Mathlib

open Function Complex Real


structure CircleImmersion (γ : ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ γ
  per : Periodic γ 1
  derive_ne : ∀ t, deriv γ t ≠ 0

/- If extra time, prove existence of lift and convert axioms to defs/lemmas -/

/-
structure CircleImmersion.lift (θ : ℝ → ℝ) : Prop where
  θ : ℝ → ℝ ???
  diff : ContDiff ℝ ⊤ θ
  expr : ∀ t, (deriv γ t = ‖deriv γ t‖ * exp (I * θ t))
-/

lemma lift_exists {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) :
  ∃ θ : ℝ → ℝ, (ContDiff ℝ ⊤ θ) ∧ (∀ (t : ℝ), (deriv γ t = ‖deriv γ t‖ * exp (I * θ t))) := sorry

def CircleImmersion.lift {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) : ℝ → ℝ :=
  sorry

variable {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ)

axiom CircleImmersion.contDiff_lift : ContDiff ℝ ⊤ imm_γ.lift

axiom CircleImmersion.deriv_eq (t : ℝ) : deriv γ t = ‖deriv γ t‖ * exp (I * imm_γ.lift t)

noncomputable def CircleImmersion.turningNumber := (imm_γ.lift 1 - imm_γ.lift 0) / (2 * π)

structure HtpyCircleImmersion (γ : ℝ → ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ (uncurry γ)
  imm : ∀ s, CircleImmersion (γ s)






lemma root_lemma_maybe : ∀ (c₁ : ℝ) (c₂ : ℝ) (c₃ : ℝ), ∃ (N : ℤ), ∃ (H : ℝ), c₁ * N * H - c₂ * H - c₃ > 0 := sorry --the constants are positive, may help to put H before N

theorem whitney_graustein {γ₀ : ℝ → ℂ} {γ₁ : ℝ → ℂ} {t : ℝ} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁) :
  (imm_γ₀.turningNumber = imm_γ₁.turningNumber) → ∃ (γ : ℝ → ℝ → ℂ), HtpyCircleImmersion γ ∧ γ 0 = γ₀ ∧ γ 1 = γ₁ := by
  intro hyp --do we want to show that since there exists some N,H pair such that... then there exists...?
  --have fact₀ : imm_γ₀.lift 1 - imm_γ₀.lift 0 = imm_γ₁.lift 1 - imm_γ₁.lift 0 := sorry
  -- extract the lifts of γ₀ and γ₁;  θs := (1−ρ(s)) θ₀ + ρ(s) θ₁ satisfies θs(1) − θs(0) ∈ 2πZ, so each Γs is periodic.
  --let θ₀ : ℝ → ℝ := imm_γ₀.lift
  --let θ₁ : ℝ → ℝ := imm_γ₁.lift
  --try to develop some lemma that if there exists some N (large enough that given H, some inequality is true), then there exists the homotopy; apply this, take that the N exists as a fact?
  rcases (lift_exists imm_γ₀) with ⟨(θ₀ : ℝ → ℝ), hθ₀⟩
  have hθ₀_diff : ContDiff ℝ ⊤ θ₀ := hθ₀.1
  have hθ₀_decomp : ∀ (t : ℝ), deriv γ₀ t = ↑‖deriv γ₀ t‖ * cexp (I * ↑(θ₀ t)) := hθ₀.2

  rcases (lift_exists imm_γ₁) with ⟨(θ₁ : ℝ → ℝ), hθ₁⟩
  have hθ₁_diff : ContDiff ℝ ⊤ θ₁ := hθ₁.1
  have hθ₁_decomp : ∀ (t : ℝ), deriv γ₁ t = ↑‖deriv γ₁ t‖ * cexp (I * ↑(θ₁ t)) := hθ₁.2

  -- have fact : ∃ N, such that some stuff is true for the maximum? of h(s) and some independent values, then ∃ γ, Htpy...
  -- apply fact
  -- falls out of root_lemma_maybe
  -- alternatively, rcases on (root_lemma_maybe K1 K2 K3) with
  let (ρ : ℝ → ℝ) := fun s ↦ s /- FOR INSTANCE -/
  let (h : ℝ → ℝ) := fun s ↦ 1 /- FOR INSTANCE -/
  let (ϝ : ℝ → ℝ → ℂ) := fun s t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
  let (φ : ℝ → ℝ → ℝ) := fun s t ↦ (1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t)
  let (R : ℝ → ℂ) := fun θ ↦ exp (I * (θ : ℝ))
  let ripple : ℝ → ℂ := fun t ↦ -Real.sin (4 * π * t) + I * 2 * Real.sin (2 * π * t)
  let (γ : ℝ → ℝ → ℂ) := fun s t ↦ ϝ s t + (h s) * (R (φ s t)) * ripple (N * t)
  have key₁ : HtpyCircleImmersion (γ : ℝ → ℝ → ℂ) := sorry

  --
  --let R : ℝ → ℂ := fun θ ↦ exp (I * θ)
  --let γ := fun s t ρ h N ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t + (h s) R(1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t) * ripple (N * t)
  -- γ s t = (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t + (h s) R(1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t) * ripple (N * t)
  sorry

-- γ s := (1 - ρ s) * γ₀ + (ρ s) * γ₁ + (h s) * (R s?) * e (N * )
-- exp (I * h.lift t) is a local homeomorphism
-- also to say that something is "independent" when constructing our lemmas...?
