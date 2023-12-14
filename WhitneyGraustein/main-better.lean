import Mathlib
import WhitneyGraustein.calculus


open Set Function Complex Real Order

open Topology NormedSpace

open Mathlib



noncomputable section

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


/-
∀K₁, K₂, K₃ : ℝ, with K₁ > 0, and ∀H > 0, we claim that  there exists some N₀ such that N ≥ N₀
implies that K₁HN - K₂H - K₃ > 0

This is required to construct our gamma function and for the main phase.
-/

lemma root_lemma_maybe (K₁ : ℝ) (K₂ : ℝ) (K₃ : ℝ) (K₁_pos : K₁ > 0) (H_pos : H > 0) : ∃ (N₀ : ℕ), ∀ N > N₀, (K₁ * H) * N - (K₂ * H + K₃) > 0 := by
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

def h : ℝ → ℝ := sorry

lemma h_diff : ContDiff ℝ ⊤ h  := sorry

lemma h_main : ∀ᶠ (x : ℝ) in 𝓝ˢ main, h x = 0 := sorry

lemma h_antimain : ∀ᶠ (x : ℝ) in 𝓝ˢ antimain, h x = H := sorry

lemma h_mem : ∀ (x : ℝ), h x ∈ Icc 0 1 := sorry

def ruffle : ℝ → ℂ := fun t ↦ ⟨-Real.sin (4 * π * t), 2 * Real.sin (2 * π * t)⟩

def R : ℝ → ℂ := fun θ ↦ cexp (θ • I)

-- See https://github.com/leanprover-community/sphere-eversion/blob/master/SphereEversion/ToMathlib/Analysis/CutOff.lean
def ρ : ℝ → ℝ := sorry

lemma ρ_diff : ContDiff ℝ ⊤ ρ := sorry

lemma ρ_ruffling : EqOn ρ 0 ruffling := sorry

lemma ρ_unruffling : EqOn ρ 1 unruffling := sorry

lemma ρ_mem : ∀ x, ρ x ∈ Icc (0 : ℝ) 1 := sorry


theorem whitney_graustein {γ₀ γ₁ : ℝ → ℂ} {t : ℝ} (imm_γ₀ : CircleImmersion γ₀) (imm_γ₁ : CircleImmersion γ₁):
  (imm_γ₀.turningNumber = imm_γ₁.turningNumber) → ∃ (γ : ℝ → ℝ → ℂ), HtpyCircleImmersion γ ∧ ((∀ t, γ 0 t = γ₀ t) ∧ (∀ t, γ 1 t = γ₁ t)) := by
  intro hyp --we want to show that since there exists some N,H pair such that... then there exists...
  -- get that unit is closed, and two disjoint closed subintervals "ruffling" and "unruffling"
  --have dfact (x : ℝ) : deriv (fun (x : ℝ) ↦ (x ^ 2)) = fun x ↦ 2 * x := by simp

  let H : ℝ := 1
  have H_pos : 0 < H := Real.zero_lt_one

  rcases (lift_exists imm_γ₀) with ⟨(θ₀ : ℝ → ℝ), hθ₀_lift_is_lift, hθ₀_diff, hθ₀_decomp⟩
  rcases (lift_exists imm_γ₁) with ⟨(θ₁ : ℝ → ℝ), hθ₁_lift_is_lift, hθ₁_diff, hθ₁_decomp⟩

  have fact {A : ℂ} : 0 = A + (-A) := by norm_num

  -- have critical : ∀ K₁ > 0, ∀ H > 0, ∀ N > N₀, ∀ s, ∀ t, ‖deriv (γ s) t‖ ≥ (K₁ s) * N * H - (K₂ s) * H - (K₃ s)
    --when we get to this part, we will need ‖A + B‖ ≥ ‖A‖ - ‖B‖; this comes from the triangle inequality: ‖A‖ + ‖B‖ ≥ ‖A + B‖ (defined for normed groups as norm_mul_le')
      --‖A + B‖ + ‖B‖ = ‖A + B‖ + ‖-B‖ ≥ ‖(A + B) + (-B)‖ = ‖A‖, so ‖A + B‖ + ‖B‖ ≥ ‖A‖, so ‖A + B‖ ≥ ‖A‖ + ‖B‖
    --from this, ‖A + B + C‖ ≥ ‖A‖ - ‖B‖ - ‖C‖ (or some rearrangement thereof)
  -- fix γ₀, γ₁, and ρ
  -- ∀ H > 0, ∃ N₀, ∀ N ≥ N₀, K₁ * N * H - K₂ * H - K₃ > 0
  -- need that ∀ s, γ s is an immersed circle (of t) (and of course, γ 0 = γ₀ and same for 1)
  -- the extreme value theorem on (1-ρ(s)) * γ₀(t) + ρ(s) * γ₁(t) provides some maximum independent of N and H that we call K₃

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

  have cont : Continuous (uncurry normB) := sorry
  rcases (unit_compact.prod unit_compact).exists_isMaxOn (unit_nonempty.prod unit_nonempty) cont.continuousOn with
    ⟨⟨s₂, t₂⟩, ⟨s₂in : s₂ ∈ unit, t₂in : t₂ ∈ unit⟩, hst₂⟩
  let K₂ := normB s₂ t₂

  let C := fun s t ↦ (2 * π) • (deriv ruffle t * R (θ s t)) --NOTICE NEITHER H NOR N IS NOT INCLUDED IN THIS STATEMENT.
  let normC := fun s t ↦ ‖C s t‖
  have cont : Continuous (uncurry normB) := sorry
  rcases (unit_compact.prod unit_compact).exists_isMinOn (unit_nonempty.prod unit_nonempty) cont.continuousOn with
    ⟨⟨s₁, t₁⟩, ⟨s₁in : s₁ ∈ unit, t₁in : t₁ ∈ unit⟩, hst₁⟩
  let K₁ := normC s₁ t₁

  have K₁_pos : K₁ > 0 := by
    sorry

  rcases (root_lemma_maybe K₁ K₂ K₃ K₁_pos H_pos) with ⟨N₀, hN₀⟩

  --Prove K₁ is positive and do the same for H (or set H = 1), get N₀, then N

  let γ : ℝ → ℝ → ℂ := fun s t ↦ ϝ s t + (h s) • (R (θ s t) * ruffle ((N₀+1) * t))
  use γ
  constructor
  --these statements will likely need to be proved out of order, probably starting with the statement of derive_ne
  · sorry
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
    · intro t
      calc
      γ 0 t = ϝ 0 t + (h 0) • (R (θ 0 t)) * ruffle ((N₀+1) * t) := sorry --dont know what to tell you... it is... B)
      _ = ϝ 0 t + 0 * (R (θ 0 t)) * ruffle ((N₀+1) * t) := sorry --h 0 = 0
      _ = ϝ 0 t + 0 := sorry --you know how it is
      _ = ϝ 0 t := sorry --naturally
      _ = (1 - (ρ 0)) * (γ₀ t) + (ρ 0) * γ₁ t := sorry --dont know what to tell you... it is... B)
      _ = (1 - 0) * (γ₀ t) + 0 * γ₁ t := sorry
      _ = 1 * (γ₀ t) + 0 := sorry
      _ = (γ₀ t) + 0 := sorry
      _ = γ₀ t := sorry
    · intro t
      calc
      γ 1 t = ϝ 1 t + (h 1) * (R (θ 1 t)) * ruffle ((N₀+1) * t) := sorry --dont know what to tell you... it is... B)
      _ = ϝ 1 t + 0 * (R (θ 1 t)) * ruffle ((N₀+1) * t) := sorry --h 0 = 0
      _ = ϝ 1 t + 0 := sorry --you know how it is
      _ = ϝ 1 t := sorry --naturally
      _ = (1 - (ρ 1)) * (γ₀ t) + (ρ 1) * γ₁ t := sorry --dont know what to tell you... it is... B)
      _ = (1 - 1) * (γ₀ t) + 1 * γ₁ t := sorry
      _ = 0 * (γ₀ t) + 1 * γ₁ t := sorry
      _ = 0 + 1 * γ₁ t := sorry
      _ = 1 * γ₁ t := sorry
      _ = γ₁ t := sorry

--Maybe of note: exp (I * h.lift t) is a local homeomorphism

end WhitneyGraustein
