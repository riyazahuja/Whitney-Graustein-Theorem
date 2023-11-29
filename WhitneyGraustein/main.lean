import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.NormedSpace.Basic


def I : Set ℝ := Set.Icc 0 1


structure ParametrizedRegularClosedCurve :=
(curve : ℝ → ℝ × ℝ)
(continuous : ContinuousOn curve I)
(differentiable : DifferentiableOn ℝ curve I)
(closed : curve 0 = curve 1 ∧ (deriv curve) 0 = (deriv curve) 1)
(regular : ∀ t:I, (deriv curve) t ≠ 0)


structure LiftOf (f : ParametrizedRegularClosedCurve) :=
(lift : ℝ → ℝ × ℝ)
(continuous : Continuous lift)
(differentiable : Differentiable ℝ lift)
(agrees : ∀ t:I, lift t = f.curve t)
(periodic : ∀ t, lift (t + 1) = lift t)
(regular : ∀ t, (deriv lift) t ≠ 0)



structure PRCC_Equiv' (f g : ParametrizedRegularClosedCurve) :=
(h : ℝ → ℝ)
(continuous : Continuous h)
(differentiable : Differentiable ℝ h)
(positive_derivative : ∀ t, deriv h t > 0)
(periodic : ∀ t, h (t + 1) = h t + 1)
(curve_relation : ∀ t:ℝ, (LiftOf g).lift t = (LiftOf f).lift (h t))
/-FIX and construct equivalence class-/



def PRCC_Equiv : ParametrizedRegularClosedCurve→ ParametrizedRegularClosedCurve → Prop :=
fun f ↦ fun g ↦ PRCC_Equiv' f g


instance  PRCC_Equiv : Equivalence :=
⟨
 -- Reflexivity proof stub
 -- Symmetry proof stub
 -- Transitivity proof stub
⟩


def RegularClosedCurve := Quotient PRCC_Equiv

/-IDK How to define equivalence relation and classes-/




/-
variable {v : ℝ × ℝ}

-- Example usage of the norm
example : ℝ := ‖v‖
-/

/-get norm from fact that ℝ² is a normed vector space-/
/-Keep norm arbitrary-/
theorem RCC_HasConstDerivativeNorm (C : RegularClosedCurve) :
  ∃ g ∈ C, ∃ L : ℝ, ∀ t, ‖(deriv g.curve) t‖ = L := sorry




theorem RCC_ConstDerivativeNorm_Characterization
  (C : rc_curve) (g ∈ C) (h ∈ C)
  (L k: ℝ)
  (hg_const : ∀ t, ‖(deriv g.curve) t‖ = L)
  (hh_const : ∀ t, ‖(deriv h.curve) t‖ = k) :
  (L = k) ∧ (∀ t, (LiftOf h).lift t = (LiftOf g).lift (t + a)) :=
sorry









structure RegularHomotopy (f0 f1 : ParametrizedRegularClosedCurve) :=
(F : ℝ × ℝ → ℝ × ℝ)
(continuous : Continuous F)
(at_zero : ∀ t, F t 0 = f0.curve t)
(at_one : ∀ t, F t 1 = f1.curve t)
(regular : ∀ u, ∃ fu : RegularClosedCurve, ∀ t, fu.curve t = F t u)

def is_regularly_homotopic (f g : ParametrizedRegularClosedCurve) : Prop :=
∃ h : RegularHomotopy f g


theorem regularly_homotopic_in_rc_curve
  {C : RegularClosedCurve} {f₀ f₁ : ParametrizedRegularClosedCurve}
  (hf₀ : f₀ ∈ C) (hf₁ : f₁ = C) :
  ∃ (F : RegularHomotopy f₀ f₁), ∀ u, quotient.mk' (F.regular u).some = C :=
sorry
