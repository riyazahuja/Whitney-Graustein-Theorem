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

lemma root_lemma_maybe {K₁ K₂ K₃: ℝ} (K₁_pos : K₁ > 0) (H_pos : H > 0) : ∃ (N₀ : ℕ), ∀ N > N₀, (K₁ * H) * N - (K₂ * H + K₃) > 0 := by
  let K₁H_pos := Real.mul_pos K₁_pos H_pos
  use Nat.floor ((K₃ + K₂ * H) / (K₁ * H) + 1)
  intro N hN
  have fact'₂ : K₁ * H * ((K₃ + K₂ * H) / (K₁ * H)) = (K₃ + K₂ * H) := mul_div_cancel' (K₃ + K₂ * H) (ne_of_gt K₁H_pos)
  have fact₃ : K₁ * H * ((K₃ + K₂ * H) / (K₁ * H)) + (K₁ * H) = (K₃ + K₂ * H) + (K₁ * H) := congrFun (congrArg HAdd.hAdd fact'₂) (K₁ * H)
  have fact₄₇ : (K₁ * H) * ((K₃ + K₂ * H) / (K₁ * H) + 1) = (K₃ + K₂ * H) + (K₁ * H) := (Eq.congr (mul_add_one (K₁ * H) ((K₃ + K₂ * H) / (K₁ * H))) rfl).mpr fact₃
  have facttt : (K₃ + K₂ * H) + (K₁ * H) < (K₁ * H) * ↑N := Eq.trans_lt (id fact₄₇.symm) ((mul_lt_mul_left K₁H_pos).mpr ((Nat.floor_lt' (Nat.not_eq_zero_of_lt hN)).1 hN))
  have factttt : K₃ + K₂ * H < K₁ * H * ↑N := gt_trans (sub_lt_self (K₁ * H * ↑N) K₁H_pos) (lt_tsub_iff_right.mpr facttt)
  exact sub_pos.mpr ((Eq.trans_lt (id (add_comm K₃ (K₂ * H)).symm)) factttt)
  -- proof, indeed.

theorem whitney_graustein {γ₀ γ₁ : ℝ → ℂ} {t : ℝ} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁) :
  (imm_γ₀.turningNumber = imm_γ₁.turningNumber) → ∃ (γ : ℝ → ℝ → ℂ), HtpyCircleImmersion γ ∧ (γ 0 = γ₀ ∧ γ 1 = γ₁) := by
  intro hyp --we want to show that since there exists some N,H pair such that... then there exists...
  -- get that unit is closed, and two disjoint closed subintervals "ruffling" and "unruffling"
  let unit : Set ℝ := Set.Icc 0 1
  let ruffling : Set ℝ := Set.Icc 0 (1/4)
  let unruffling : Set ℝ := Set.Icc (3/4) 1
  let main : Set ℝ := Set.Icc (1/4) (3/4)
  let antimain : Set ℝ := (Set.Iic 0) ∪ (Set.Ici 1)

  have ruffling_closed : IsClosed (Set.Icc 0 (1/4)) := isClosed_Icc
  have unruffling_closed : IsClosed (Set.Icc (3/4) 1) := isClosed_Icc
  have main_closed : IsClosed (Set.Icc (1/4) (3/4)) := isClosed_Icc

  have ruffling_unruffling_disjoint : Disjoint ruffling unruffling := sorry
  have main_antimain_disjoint : Disjoint main antimain := sorry

  --The below lemmas depend on here: https://github.com/leanprover-community/sphere-eversion/blob/master/SphereEversion/ToMathlib/Analysis/CutOff.lean
  have cutoff_exists : ∃ ρ : ℝ → ℝ, ContDiff ℝ ⊤ ρ ∧ EqOn ρ 0 ruffling ∧ EqOn ρ 1 unruffling ∧ ∀ x, ρ x ∈ Icc (0 : ℝ) 1 := sorry--exists_contDiff_zero_one (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t)
  rcases cutoff_exists with ⟨ρ, hρ⟩
  have fact : ∃ (H : ℝ), H > 0 := Exists.intro 1 Real.zero_lt_one
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
  -- the extreme value theorem on (1-ρ(s)) * γ₀(t) + ρ(s) * γ₁(t) provides some maximum independent of N and H that we call K₃

  let (ϝ : ℝ → ℝ → ℂ) := fun s t ↦ (1 - (ρ s)) * (γ₀ t) + (ρ s) * γ₁ t
  let (θ : ℝ → ℝ → ℝ) := fun s t ↦ (1 - (ρ s)) * (θ₀ t) + (ρ s) * (θ₁ t)

  let (R : ℝ → ℂ) := fun θ ↦ exp (I * (θ : ℝ))
  let ruffle : ℝ → ℂ := fun t ↦ -Real.sin (4 * π * t) + I * 2 * Real.sin (2 * π * t)
  let (γ : ℝ → ℝ → ℂ) := fun s t ↦ ϝ s t + (h s) * (R (θ s t)) * ruffle (N * t)
  use γ
  constructor
  --these statements will likely need to be proved out of order, probably starting with the statement of derive_ne
  · sorry --HtpyCircleImmersion (γ : ℝ → ℝ → ℂ)
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
        --do we need a lemma (hopefully something similar in mathlib or otherwise eliminative of the issue of separating into "phases"):
          --for all a c : ℝ for all γ ContDiff on [a, c], for all b with a < b < c, if deriv γ t ≠ 0 on (a, b) and deriv γ t ≠ 0 on (b, c) and deriv γ b ≠ 0, then deriv γ t ≠ 0 on (a, b)
            --or some other lemma that relates extrema on two intervals to extrema on their union (or otherwise to that effect)
          --NOTE that the deriv γ b condition can be substituted for being monotonic on some neighborhood of b,
            --which if we take for granted, could make handling the cutoff nice if we just assert it is entirely nondecreasing (or maybe im tripping)
        --do we want to prove this with explicit values for the given R and ruffle (and h and ρ) (anything else?) first or do we want to prove the more general statements of their existence
        --for a given s, K₁ = min of the norm of the thing with h and N in it
          --exists cuz norm has clear lower bound 0, show that this in particular is nonzero because the terms are nonnegative and are never simultaneously zero
        --for a given s, K₂ = max(‖h * deriv (θ s) * R * ruffle‖) on s, t ∈ [0, 1]
          --exists since everything is bounded
        --for a given s, K₃ = max(‖(1 - ρ s) * (γ₀ t) + (ρ s) * (γ₁ t)‖) on s, t ∈ [0, 1]
          --exists since (ρ s) and γ₀ and γ₁ are all bounded on the period, etc or whatever
        --using root_lemma_maybe (or whatever it renamed to), get N₀ and define γ, carry out some triangle inequality argument showing that ∀ s, ‖deriv (γ s) t‖ > 0, and hence nonzero.
  · constructor
    · sorry --γ 0 = γ₀
    · sorry --γ 1 = γ₁

--Maybe of note: exp (I * h.lift t) is a local homeomorphism
