import Mathlib

open Set Function Complex Real

open Topology


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

def CircleImmersion.lift {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) : ℝ → ℝ := sorry

lemma lift_exists {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ) :
  ∃ θ : ℝ → ℝ, (θ = CircleImmersion.lift imm_γ) ∧ (ContDiff ℝ ⊤ θ) ∧ (∀ (t : ℝ), (deriv γ t = ‖deriv γ t‖ * exp (I * θ t))) := sorry

-- Lift unique?


variable {γ : ℝ → ℂ} (imm_γ : CircleImmersion γ)

axiom CircleImmersion.contDiff_lift : ContDiff ℝ ⊤ imm_γ.lift

axiom CircleImmersion.deriv_eq (t : ℝ) : deriv γ t = ‖deriv γ t‖ * Complex.exp (I * imm_γ.lift t)

noncomputable def CircleImmersion.turningNumber := (imm_γ.lift 1 - imm_γ.lift 0) / (2 * π)

structure HtpyCircleImmersion (γ : ℝ → ℝ → ℂ) : Prop where
  diff : ContDiff ℝ ⊤ (uncurry γ)
  imm : ∀ s, CircleImmersion (γ s)

lemma root_lemma_maybe : ∀ (c₁ : ℝ) (c₂ : ℝ) (c₃ : ℝ), ∃ (N : ℤ), ∃ (H : ℝ), c₁ * N * H - c₂ * H - c₃ > 0 := sorry --the constants are positive, may help to put H before N

theorem whitney_graustein {γ₀ γ₁ : ℝ → ℂ} {t : ℝ} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁) :
  (imm_γ₀.turningNumber = imm_γ₁.turningNumber) → ∃ (γ : ℝ → ℝ → ℂ), HtpyCircleImmersion γ ∧ (γ 0 = γ₀ ∧ γ 1 = γ₁) := by
  intro hyp --do we want to show that since there exists some N,H pair such that... then there exists...?
  -- get that unit is closed, and two disjoint closed subintervals "ruffling" and "unruffling"
  let unit : Set ℝ := Set.Icc 0 1
  let ruffle : Set ℝ := Set.Icc 0 (1/4)
  let unruffle : Set ℝ := Set.Icc (3/4) 1
  let main : Set ℝ := Set.Icc (1/4) (3/4)
  let antimain : Set ℝ := (Set.Iic 0) ∪ (Set.Ici 1)

  have ruffle_closed : IsClosed (Set.Icc 0 (1/4)) := isClosed_Icc
  have unruffle_closed : IsClosed (Set.Icc (3/4) 1) := isClosed_Icc
  have main_closed : IsClosed (Set.Icc (1/4) (3/4)) := isClosed_Icc

  have ruffle_unruffle_disjoint : Disjoint ruffle unruffle := sorry
  have main_antimain_disjoint : Disjoint main antimain := sorry

  --The below lemmas depends on some definition I cant find in mathlib, assumedly somewhere in here: https://github.com/leanprover-community/sphere-eversion/blob/master/SphereEversion/ToMathlib/Analysis/CutOff.lean
  have cutoff_exists : ∃ ρ : ℝ → ℝ, ContDiff ℝ ⊤ ρ ∧ EqOn ρ 0 ruffle ∧ EqOn ρ 1 unruffle ∧ ∀ x, ρ x ∈ Icc (0 : ℝ) 1 := sorry--exists_contDiff_zero_one (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t)
  rcases cutoff_exists with ⟨ρ, hρ⟩
  have fact : ∃ (H : ℝ), H > 0 := sorry
  rcases fact with ⟨H, hH⟩
  have bump_exists : ∃ h : ℝ → ℝ, ContDiff ℝ ⊤ h ∧ (∀ᶠ x in 𝓝ˢ main, h x = 0) ∧ (∀ᶠ x in 𝓝ˢ antimain, h x = H) ∧ ∀ x, h x ∈ Icc (0 : ℝ) 1 := sorry--exists_contDiff_zero_one_nhds (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t)
  rcases bump_exists with ⟨h, hh⟩

  rcases (lift_exists imm_γ₀) with ⟨(θ₀ : ℝ → ℝ), hθ₀⟩
  have hθ₀_lift_is_lift : θ₀ = CircleImmersion.lift imm_γ₀ := hθ₀.1
  have hθ₀_diff : ContDiff ℝ ⊤ θ₀ := hθ₀.2.1
  have hθ₀_decomp : ∀ (t : ℝ), deriv γ₀ t = ↑‖deriv γ₀ t‖ * cexp (I * ↑(θ₀ t)) := hθ₀.2.2

  rcases (lift_exists imm_γ₁) with ⟨(θ₁ : ℝ → ℝ), hθ₁⟩
  have hθ₁_lift_is_lift : θ₁ = CircleImmersion.lift imm_γ₁ := hθ₁.1
  have hθ₁_diff : ContDiff ℝ ⊤ θ₁ := hθ₁.2.1
  have hθ₁_decomp : ∀ (t : ℝ), deriv γ₁ t = ↑‖deriv γ₁ t‖ * cexp (I * ↑(θ₁ t)) := hθ₁.2.2

  -- have critical : ∃ K₁ > 0, K₂ ≥ 0, K₃ ≥ 0, ∀ H, ∀ N, ∀ s, t, ‖deriv γ s t (wrt t)‖ ≥ K₁ * N * H - K₂ * H - K₃
  -- fix γ₀, γ₁, and ρ
  -- ∀ H > 0, ∃ N₀, ∀ N ≥ N₀, K₁ * N * H - K₂ * H - K₃ > 0
  -- need that ∀ s, γ s is an immersed circle (of t) (and of course, γ 0 = γ₀ and same for 1)
  -- the extreme value theorem on 1-ρ(s)... provides some maximum independent of N and H that we call K₃? i think?

  let (ϝ : ℝ → ℝ → ℂ) := fun s t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
  let (θ : ℝ → ℝ → ℝ) := fun s t ↦ (1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t)

  let (R : ℝ → ℂ) := fun θ ↦ exp (I * (θ : ℝ))
  let ruffling : ℝ → ℂ := fun t ↦ -Real.sin (4 * π * t) + I * 2 * Real.sin (2 * π * t)
  let (Γ : ℝ → ℝ → ℂ) := fun s t ↦ ϝ s t + (h s) * (R (θ s t)) * ruffling (N * t)
  use γ
  constructor
  · sorry --HtpyCircleImmersion (γ : ℝ → ℝ → ℂ)
    --requires diff : ContDiff ℝ ⊤ (uncurry γ)
    -- requires imm : ∀ s, CircleImmersion (γ s)
      --requires diff : ContDiff ℝ ⊤ (γ s)
      --requires per : Periodic (γ s) 1
        --requires ∀ t, (γ s) (t + 1) = (γ s) t
          --(ϝ s) := fun t ↦ t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
          --(θ s) := t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
          --(γ s) := fun t ↦ (ϝ s) t + (h s) * (R ((θ s) t)) * ripple (N * t)
          --       = fun t ↦ (fun t ↦ t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t) t + (h s) * (R ((t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t) t)) * ruffle (N * t)
      --requires derive_ne : ∀ t, deriv γ t ≠ 0
  · constructor
    · sorry --γ 0 = γ₀
    · sorry --γ 1 = γ₁
  have diff : ContDiff ℝ ⊤ (uncurry γ) := sorry
  have imm : ∀ s, CircleImmersion (γ s)
  have key₁ : HtpyCircleImmersion (γ : ℝ → ℝ → ℂ) := sorry

  --
  --let R : ℝ → ℂ := fun θ ↦ exp (I * θ)
  --let γ := fun s t ρ h N ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t + (h s) R(1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t) * ripple (N * t)
  -- γ s t = (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t + (h s) R(1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t) * ripple (N * t)
  sorry

-- γ s := (1 - ρ s) * γ₀ + (ρ s) * γ₁ + (h s) * (R s?) * e (N * )
-- exp (I * h.lift t) is a local homeomorphism
-- also to say that something is "independent" when constructing our lemmas...?
