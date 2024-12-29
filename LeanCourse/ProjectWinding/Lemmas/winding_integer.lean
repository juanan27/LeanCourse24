import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.GroupWithZero.Basic
import LeanCourse.ProjectWinding.Definitions.curves

open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

-- We can see the complex plane divided by the interior, exterior and image of any closed curve:

lemma interior_exterior_OfClosedCurve_whole_plane (γ : closed_curve) :
∀ z : ℂ, z ∈ interiorOfClosedCurve γ ∪ exteriorOfClosedCurve γ ∪ imageOfClosedCurve γ := by {
  intro z
  by_cases h : z ∈ γ '' I
  · exact Set.mem_union_right (interiorOfClosedCurve γ ∪ exteriorOfClosedCurve γ) h
  · by_cases h₀ : ω z γ = 0
    · have h₀' : z ∈ exteriorOfClosedCurve γ := by {
      unfold exteriorOfClosedCurve
      simp only [Set.mem_Icc, not_exists, not_and, and_imp, mem_setOf_eq]
      trivial
      }
      simp[h₀']
    · have h₀' : z ∈ interiorOfClosedCurve γ := by {
      unfold interiorOfClosedCurve
      simp only [Set.mem_Icc, not_exists, not_and, and_imp, mem_setOf_eq]
      trivial}
      simp[h₀']

}

lemma disjoint_interior_exterior_OfClosedCurve (γ : closed_curve):
interiorOfClosedCurve γ ∩ exteriorOfClosedCurve γ ∩ imageOfClosedCurve γ = ∅ := by {
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, and_imp]
  intro h₀ h₁
  exfalso
  have h0 : ω z γ = 0 := by {
    unfold exteriorOfClosedCurve at *
    have haux : ω z γ = 0 ∧ z ∉ γ.toFun '' I := by exact h₁
    obtain ⟨hp, hq⟩ := haux
    exact hp
  }
  have h1 : ω z γ ≠ 0 := by {
    unfold interiorOfClosedCurve at *
    have haux : ω z γ ≠  0 ∧ z ∉ γ.toFun '' I := by exact h₀
    obtain ⟨hp, hq⟩ := haux
    exact hp
  }
  contradiction
}


-- The index function is continuous

theorem ω_cont (γ : closed_curve) (z : ℂ) (h : ∀ t ∈ I, γ t ≠ z)
: ContinuousOn ω (univ \ (image γ I))  := by {
  intro z₀ hz₀
  unfold ω
  simp
  intro x hx
  simp
  sorry
}
theorem division_continuous (f : ℝ → ℂ ) (g : ℝ → ℂ ) (h : ContinuousOn f (I))
(h' : ContinuousOn g (I)) (h_v : ∀ s ∈ I, g s ≠ 0) : ContinuousOn (fun s ↦ f s / g s) (I) := by {
apply h.div
exact h'
exact fun x a ↦ h_v x a
}

lemma ftc (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

lemma ftc_2 (f : ℝ → ℂ) (hf : ContinuousOn f (I))
    (g : ℝ → ℂ := fun u ↦ ∫ x : ℝ in (0)..u, f x) : ∀ b ∈ I, deriv g b = f b :=
  by {
    intro b hb
    sorry
    }


-- We prove now that the winding number is always an integer. We introduce the following lemma:

lemma exp_one (z : ℂ) (h_1 : Complex.exp z = 1) : ∃ k : ℤ, z = 2 * Real.pi * k * Complex.I := by {
  have h : Complex.exp z = 1 → ∃ n : ℤ , z = n * (2 * ↑π * Complex.I) := by exact Complex.exp_eq_one_iff.1
  have h' : ∃ n : ℤ , z = ↑n * (2 * ↑π * Complex.I) := h h_1
  obtain ⟨ n, hn ⟩ := h'
  use n
  simp[hn]
  ring
  }

-- We are ready to show ω is an integer

theorem ω_integer (γ : closed_curve) (z : ℂ) (h : ∀ t ∈ I , γ t ≠ z)
: ∃ n : ℤ, ω z γ = n := by {
  unfold ω
  have hz : ContinuousOn (fun s : ℝ  ↦ z) (I) := by exact continuousOn_const
  have hγ : ContinuousOn (fun s : ℝ ↦ γ s) (I) := by exact curve.ContOn γ.tocurve
  let g' := fun s : ℝ ↦ γ s - z
  have hg' : ContinuousOn g' (I) := by {
  simp_all only [ne_eq, g']
  exact ContinuousOn.sub hγ hz
  }
  let g := fun t : ℝ  => ∫ s in (0)..(t), (deriv γ s) / (γ s - z)
  let h' := fun s : ℝ ↦ deriv γ s
  have hg : ContinuousOn h' (I) := by {
  exact curve.Cont_derivOn γ.tocurve
  }
  have h_vanish : ∀ s ∈ I, g' s ≠ 0 := by exact fun s a ↦ sub_ne_zero_of_ne (h s a)
  let φ := fun s : ℝ ↦ (h' s / g' s)
  have h_cont : ContinuousOn φ (I) := by {
    exact division_continuous h' g' hg hg' h_vanish
  }
  have hg'' : ∀ t ∈ I, deriv g t = (deriv γ t) / (γ t - z) := by {
  intro t ht
  apply ftc_2
  · exact h_cont
  · exact ht
  }
  let ψ : ℝ → ℂ := fun t ↦ Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * (γ t - z)
  have deriv₀ : ∀ t ∈ I, deriv ψ t = 0 := by {
    intro t ht
    --have hψ : ψ t = Complex.exp (-g t ) * (γ t - z) := by exact rfl
    calc
      deriv ψ t
        = deriv (fun t ↦ Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z))) t * (γ t - z)
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv (fun t ↦ γ t - z) t := by {
          have h₁ : DifferentiableAt ℝ (fun y ↦ γ.toFun y - z) t := by {
            simp_all only [Set.mem_Icc, ne_eq, and_imp, differentiableAt_const,
            DifferentiableAt.sub_iff_left, g', h',
              φ, g]
            have h_diff := γ.diff_curve
            have hI : t ∈ I := by exact ht
            have hNeigh : I ∈ nhds t := by sorry
            exact DifferentiableOn.differentiableAt h_diff hNeigh
          }
          apply deriv_mul
          sorry
          sorry
        }
    _ = (- Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * (deriv γ t / (γ t - z))) * (γ t - z)
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          sorry
        }
    _ = -Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          have h1 : (deriv γ t / (γ t - z)) * (γ t - z) = deriv γ t := by {exact div_mul_cancel₀ (deriv γ.toFun t) (h_vanish t ht)}
          sorry
        }
    _ = 0 := by ring
    }
  have coincide_ψ : ψ 0 = ψ 1 := by {
    have h_const : ∀ t ∈ Set.Icc 0 1, ψ t = ψ 0 := by {
    intro t ht

    --let h_const := funext (λ t ↦ deriv₀ t (Set.mem_Icc.mpr ⟨le_of_lt ?_, le_of_lt ?_⟩))
    --calc
      --ψ 0 = ψ 1 := by rw [h_const]
  }
  }

  simp_rw[ψ] at coincide_ψ
  have hψ₀ : ψ 0 = γ.toFun 0 - z := by {
    have hg_0 : g 0 = 0 := by exact intervalIntegral.integral_same
    have hg__0 : -g 0 = 0 := by simp[hg_0]
    have exp_g : Complex.exp (-g 0) = 1 := by simp[hg__0]
    simp_rw[ψ]
    simp_rw[exp_g]
    simp
  }
  have hψ₁ : ψ 1 = Complex.exp (-g 1) * (γ.toFun 0 - z) := by simp[γ.closed]
  have h_simp : (γ.toFun 0 - z) = Complex.exp (-g 1) * (γ.toFun 0 - z)  := by {
    nth_rewrite 1 [← hψ₀]; rw[← hψ₁]; exact coincide_ψ
  }
  have hexp: Complex.exp (-g 1) = 1 := by {
    have h_dist : γ.toFun 0 ≠ z := by {
      specialize h 0
      have h_0 : 0 ∈ I := by exact unitInterval.zero_mem
      exact h h_0
    }
    have h_distinct : γ.toFun 0 - z ≠ 0 := by exact sub_ne_zero_of_ne h_dist
    simp[h_distinct] at h_simp
    exact h_simp
  }
  have h_g : ∃ n : ℤ, -g 1 = 2 * Real.pi * n * Complex.I := by {
    exact exp_one (z := -g 1) (h_1 := hexp)
  }
  simp_rw[g] at *
  have h_minus : ∃ n : ℤ, ∫ (s : ℝ) in (0).. 1, deriv γ.toFun s / (γ.toFun s - z) = 2 * ↑π * ↑n * Complex.I := by {
    obtain ⟨k, hk⟩ := h_g
    use -k
    push_cast
    simp[hk]
    rw[← hk]
    ring
  }
  obtain ⟨m, hm⟩ := h_minus
  -- It is sufficient to prove the following:
  have hsuff : ∃ n : ℤ, ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = 2 * Real.pi * ↑n * Complex.I := by {
    have h_eq : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z) := by {
      rw [intervalIntegral.integral_of_le]
      have h': [[0, 1]] = I := by refine uIcc_of_le ?h; linarith
      rw[← h']
      simp[Eq.symm integral_Icc_eq_integral_Ioc]
      linarith
    }
    use m
    simp[h_eq, hm]
    }
  have not_zero : (2 * ↑π * Complex.I) ≠ 0 := by {
    simp
    exact pi_ne_zero
  }
  field_simp[hsuff, not_zero]
  have h_equal : ∀ n : ℤ, (n : ℂ) * (2 * ↑π * Complex.I) = 2 * ↑π * (n:ℂ ) * Complex.I := by {
    intro n
    ring
  }
  simp[h_equal]
  exact hsuff
}
-- DISCRETE WINDING NUMBER??
#check constant_of_derivWithin_zero
#check Continuous.deriv_integral
