import Mathlib.Analysis.Calculus.ContDiff.Basic

open Function

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp] lemma fderiv_prod_mk (x : E) (y : F) : fderiv 𝕜 (Prod.mk x) y = ContinuousLinearMap.inr 𝕜 E F := by
  rw [(hasFDerivAt_prod_mk_right (𝕜 := 𝕜) x y).fderiv]

variable {𝕜}

lemma ContDiff.continuous_partial_snd {f : E → 𝕜 → F} {n : ℕ∞} (hf : ContDiff 𝕜 n (uncurry f)) (hn : 1 ≤ n) :
    Continuous (fun x : E × 𝕜 ↦ deriv (f x.1) x.2) := by
  have : ∀ s t, deriv (f s) t = fderiv 𝕜 (uncurry f) (s, t) (0, 1) := by
    intro s t
    have : f s = uncurry f ∘ (fun t  ↦ (s, t)) := by ext1 t ; rfl
    rw [← fderiv_deriv, this, fderiv.comp, fderiv_prod_mk, ContinuousLinearMap.comp_apply]
    · simp
    · exact hf.differentiable hn _
    · exact (contDiff_prod_mk_right s).differentiable le_top _
  simpa [this] using (ContinuousLinearMap.apply 𝕜 F ((0, 1) : E × 𝕜)).continuous.comp (hf.continuous_fderiv hn)
