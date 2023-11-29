
import Mathlib
open Function Complex Real


structure IsCircleImmersion (γ:ℝ→ℂ): Prop where
  diff:ContDiff ℝ ⊤ γ
  per : Periodic γ 1
  derive_ne : ∀ t, deriv γ t ≠ 0


/-If extra time, prove existence of lift and convert axioms to defs/lemmas -/

lemma lift_exists {γ} (hγ : IsCircleImmersion γ) : ∃L : ℝ→ ℝ,
(ContDiff ℝ ⊤ h.lift) ∧  (deriv γ t = ‖deriv γ t‖ * exp (I*h.lift t)) := sorry


def IsCircleImmersion.lift {γ:ℝ→ℂ} (h:IsCircleImmersion γ) : ℝ → ℝ := by
  rcases lift_exists h with ⟨L,hL_c1, hL_deq⟩

variable {γ:ℝ→ℂ} (h:IsCircleImmersion γ)

axiom IsCircleImmersion.contDiff_lift : ContDiff ℝ ⊤ h.lift

axiom IsCircleImmersion.deriv_eq_lift (t:ℝ): deriv γ t = ‖deriv γ t‖ * exp (I*h.lift t)


noncomputable def IsCircleImmersion.turningNumber := (h.lift 1 - h.lift 0)/(2*π)

structure IsHtpyCircleImmersion (γ: ℝ → ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ (uncurry γ)
  imm : ∀ s, IsCircleImmersion (γ s)


theorem whitney_graustein {γ₀ γ₁} (h₀ : IsCircleImmersion γ₀) (h₁ : IsCircleImmersion γ₁)
(h: h₀.turningNumber = h₁.turningNumber) :
∃ γ : ℝ → ℝ → ℂ, IsHtpyCircleImmersion γ ∧ γ 0 = γ₀ ∧ γ 1 = γ₁ :=
sorry
