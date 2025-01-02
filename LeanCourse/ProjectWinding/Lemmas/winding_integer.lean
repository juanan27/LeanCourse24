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
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.GroupWithZero.Basic
import LeanCourse.ProjectWinding.Definitions.curves

open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
--open scoped Real NNReal Interval Pointwise Topology
open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics
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

theorem division_continuous_ball (f : ℂ → ℂ ) (g : ℂ → ℂ ) (h : ContinuousOn f (closedBall 0 1))
(h' : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ f s / g s) (closedBall 0 1) := by {
  apply h.div
  exact h'
  exact fun x a ↦ h_v x a}

theorem inverse_continuous_ball (g : ℂ → ℂ)
(h : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ 1 / g s) (closedBall 0 1) := by {
  let f : ℂ → ℂ := fun z ↦ 1
  have hf : ContinuousOn f (closedBall 0 1) := by exact continuousOn_const
  have hquot : ContinuousOn (fun s ↦ f s / g s) (closedBall 0 1) := by exact division_continuous_ball f g hf h h_v
  exact hquot
}

-- We write the same theorems in the differentiable version

theorem division_differentiable (f : ℂ → ℂ ) (g : ℂ → ℂ ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g ) (h₀ : ∀ z, g z ≠ 0):
 Differentiable ℂ (fun s ↦ f s / g s) := by {
  apply hf.div
  trivial
  tauto
 }

theorem inverse_differentiable (g : ℂ → ℂ)
(h : Differentiable ℂ g ) (h_v : ∀ s, g s ≠ 0) : Differentiable ℂ (fun s ↦ 1 / g s)  := by {
let f : ℂ → ℂ := fun z ↦ 1
have hf : Differentiable ℂ f := by exact differentiable_const 1
have hqout : Differentiable ℂ (fun s ↦ 1 / g s) := by exact division_differentiable (fun s ↦ 1) g hf h h_v
exact hqout
}

theorem division_differentiable_ball (f : ℂ → ℂ ) (g : ℂ → ℂ ) (hf : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ f z_1) (hg : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1 ) (h₀ : ∀ z, g z ≠ 0):
 ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ f s / g s) z_1 := by {
  intro z_1 h_z1
  specialize hf z_1 h_z1
  specialize hg z_1 h_z1
  apply hf.div
  · exact hg
  · tauto
 }

theorem inverse_differentiable_ball (g : ℂ → ℂ)
(h : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ 1 / g s) s  := by {
  let f : ℂ → ℂ := fun z ↦ 1
  intro s hs
  have hf : ∀ s ∈ closedBall 0 1, DifferentiableAt  ℂ f s := by exact fun s a ↦ differentiableAt_const 1
  have hquot : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ  (fun s ↦ f s / g s) s := by exact fun s a ↦ DifferentiableAt.div (hf s a) (h s a) (h_v s a)
  exact hquot s hs
  }

lemma ftc (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

lemma ftc_2 (f : ℝ → ℂ) (hf : ContinuousOn f (I))
    (g := fun u ↦ ∫ x : ℝ in (0)..u, f x) : ∀ b ∈ I, deriv g b = f b :=
  by {
    intro b hb
    have h_deriv : HasDerivAt g (f b) b := by {
      sorry
    }
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
            have hNeigh : I ∈ nhds t := by sorry -- would be ideal to use DifferentiableOn.differentiableAt
            exact DifferentiableOn.differentiableAt h_diff hNeigh
          }
          apply deriv_mul
          · have haux : DifferentiableAt ℝ (fun y ↦ - ∫ (s : ℝ) in (0)..y, deriv γ.toFun s / (γ.toFun s - z)) t := by {
            simp_all only [and_imp, differentiableAt_const, DifferentiableAt.sub_iff_left,
              differentiableAt_neg_iff, g', h', φ, g]
            have hintg : ∀ t ∈ I, IntervalIntegrable (fun t => deriv γ.toFun t / (γ.toFun t - z)) MeasureTheory.volume (0) t := by {
              intro t ht
              apply ContinuousOn.intervalIntegrable
              have h_sub : Icc 0 t ⊆ I := by {
                intro x hx
                obtain ⟨h₀, h₁⟩ := hx
                have h₂ : t ≤ 1 := by simp_all only [Set.mem_Icc, ne_eq, and_imp]
                have h₃ : 0 ≤ t := by simp_all only [Set.mem_Icc, ne_eq, and_imp, and_true]
                have h₄ : x ≤ 1 := by exact le_trans h₁ h₂
                simp_all only [Set.mem_Icc, ne_eq, and_imp, and_self]
              }
              rename_i ht_1
              simp_all only [Set.mem_Icc, ne_eq, and_imp, Set.uIcc_of_le]
              exact h_cont.mono h_sub
            }
            sorry
        }
    _ = - Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t / (γ t   - z) * (γ t - z)
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          sorry
        }
    _ = -Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          rw [div_mul_cancel₀
              (-Complex.exp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
                deriv γ.toFun t)
              (h_vanish t ht)]
        }
    _ = 0 := by ring
    }
  have coincide_ψ : ψ 0 = ψ 1 := by {
    have h_cont : ContinuousOn (fun t ↦ deriv γ.toFun t / (γ.toFun t - z)) I := by sorry
    have hcont : ContinuousOn ψ I := by {
      refine ContinuousOn.mul ?_ ?_
      · have hF : ContinuousOn (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) I := by {
        apply ContinuousOn.neg
        sorry
        }
        exact ContinuousOn.cexp hF
      · exact ContinuousOn.sub hγ (continuousOn_const)
    }
    have hderiv : ∀ t ∈ Set.Ico 0 1, HasDerivWithinAt ψ 0 (Set.Ici t) t := by {
      intro t ht
      have htt : t ∈ I := by exact mem_Icc_of_Ico ht
      have h_deriv : deriv ψ t = 0 := deriv₀ t htt
      obtain ⟨h₁, h₂⟩ := ht
      sorry
    }
    have h_const : ∀ x ∈ Set.Icc 0 1, ψ x = ψ 0 := by {
      intro x hx
      exact constant_of_has_deriv_right_zero hcont hderiv x hx
    }
    simp_all only [Set.mem_Icc, ne_eq, and_imp, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, one_mul,
      le_refl, zero_le_one, g', h', φ, g, ψ]
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

-- We evaluate the values of ω when γ is the unit circle:

-- First we show the following useful equality:

lemma contour_integral_eq_curve_integral (γ : closed_curve) (h_circle : ∀ t ∈ I, γ t = Complex.exp (Complex.I * 2*π* t)) (z : ℂ ) (g : ℂ → ℂ := fun z_1 ↦ 1 / (z_1 - z)):
∫ (t : ℝ) in I, deriv γ t / (γ t - z) = ∮ (z_1 : ℂ) in C(0, 1), g z_1 := by {
        rw[circleIntegral_def_Icc]
        unfold circleMap
        simp
        have hsubs : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∫ (t : ℝ) in I, deriv γ.toFun t / (cexp («I» * 2 * ↑π * ↑t) - z) := by {
          refine setIntegral_congr_ae₀ ?hs ?h -- should be easy to show
          · exact nullMeasurableSet_Icc
          · have haux : ∀ x ∈ I, deriv γ.toFun x / (γ.toFun x - z) = deriv γ.toFun x / (cexp («I» * 2 * ↑π * ↑x) - z) := by exact fun x a ↦ congrArg (HDiv.hDiv (deriv γ.toFun x)) (congrFun (congrArg HSub.hSub (h_circle x a)) z)
            exact ae_of_all volume haux
        }
        rw[hsubs]
        have hsubs_2 : ∫ (t : ℝ) in I, deriv γ.toFun t / (cexp («I» * 2 * ↑π * ↑t) - z) = ∫ (t : ℝ) in I, deriv cexp («I» * 2 * ↑π * ↑t) / (cexp («I» * 2 * ↑π * ↑t) - z) := by {
          refine setIntegral_congr_ae₀ ?hs ?_
          have haux : ∀ x ∈ I, deriv γ.toFun x = deriv cexp («I» * 2 * ↑π * ↑x) := by {
            intro x hx
            specialize h_circle x hx
            refine ftc_2 (fun x ↦ deriv cexp («I» * 2 * ↑π * ↑x)) ?hf γ.toFun x hx
            refine Continuous.comp_continuousOn' ?hf.hg ?hf.hf
            have hexp : deriv cexp = cexp := by exact Complex.deriv_exp
            rw[hexp]
            exact Complex.continuous_exp
            fun_prop
            }
          have haux_final : ∀ x ∈ I, deriv γ.toFun x / (cexp («I» * 2 * ↑π * ↑x) - z) = deriv cexp («I» * 2 * ↑π * ↑x) / (cexp («I» * 2 * ↑π * ↑x) - z) := by exact fun x a ↦ congrFun (congrArg HDiv.hDiv (haux x a)) (cexp («I» * 2 * ↑π * ↑x) - z)
          exact ae_of_all volume haux_final
          }
        rw[hsubs_2]
        have hθ : ∀ θ ∈ Set.Icc 0 (2 * π), deriv (fun θ ↦ cexp (↑θ * «I»)) θ = Complex.I * cexp (↑θ * «I») := by {
          intro θ hθ
          let f : ℝ → ℂ := (fun θ ↦ (↑θ * «I»))
          have hdiff : DifferentiableAt ℝ f θ := by {
            simp_rw[f]
            apply DifferentiableAt.mul_const
            sorry
          }
          rw[deriv_cexp hdiff (f := f)]
          have hderiv : deriv f θ = Complex.I := by {
            simp_rw[f]
            sorry

          }
          rw[hderiv]
          simp_rw[f]
          ring
        }
        have haux : ∀ θ ∈ Set.Icc 0 (2 * π), deriv (fun θ ↦ cexp (↑θ * «I»)) θ * g (cexp (↑θ * «I»)) = Complex.I * cexp (↑θ * «I») * g (cexp (↑θ * «I»)) := by sorry
        --refine setIntegral_congr_ae₀ ?hs ?_
        sorry
        }

lemma winding_circle_inside (γ : closed_curve) (h_circle : ∀ t ∈ I, γ t = Complex.exp (Complex.I * 2*π* t)) (z : ℂ ) (h : norm z < 1) : ω z γ = 1 := by {
  unfold ω
  have h_int : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = 2*π*Complex.I := by {
    let const : ℂ → ℂ := fun z ↦ 1
    have integ_eq : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∮ (z_1 : ℂ) in C(0, 1), (z_1 - z)⁻¹ := by {
      refine contour_integral_eq_curve_integral γ ?h_circle z fun z_1 ↦ (z_1 - z)⁻¹
      intro t ht
      specialize h_circle t ht
      trivial
    }
    rw[integ_eq]
    have hc1 : const z = 1 := by exact rfl
    have haux : 2 * ↑π * Complex.I = (2 * ↑π * Complex.I ) • const z := by norm_num[hc1]
    rw[haux]
    have haux2 : (∮ (z_1 : ℂ) in C(0, 1), (z_1 - z)⁻¹) = (∮ (z_1 : ℂ) in C(0, 1), (z_1 - z)⁻¹ • const z_1) := by norm_num
    rw[haux2]
    apply DiffContOnCl.circleIntegral_sub_inv_smul (c := 0) (R := 1) (f := const) (w := z) -- can also use circleIntegral.integral_sub_inv_of_mem_ball
    · exact diffContOnCl_const
    · exact mem_ball_zero_iff.mpr h
  }
  · rw[h_int]
    have not_zero : (2 * ↑π * Complex.I) ≠ 0:= by simp[pi_ne_zero]
    field_simp
}

  /- Outside the unit circle we can use the fact that the function is holomorphic. For this we use the lemma
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable. -/

  lemma winding_circle_outside (γ : closed_curve) (h_circle : ∀ t ∈ I, γ t = Complex.exp (Complex.I * 2*π* t)) (z : ℂ ) (h : norm z > 1) : ω z γ = 0 := by {
    unfold ω
    have h₀ : ∫ (t : ℝ) in I, deriv γ t / (γ t - z) = 0 := by {
      let g : ℂ → ℂ := fun z_1 ↦ 1 / (z_1 - z)
      have h_1 : ∫ (t : ℝ) in I, deriv γ t / (γ t - z) = ∮ (z_1 : ℂ) in C(0, 1), g z_1 := by {
        exact contour_integral_eq_curve_integral γ h_circle z g}
      rw[h_1]
      apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (s := ∅)
      · exact countable_empty
      · have hz_1 : ∀ z_1 ∈ (closedBall 0 1), z_1 - z ≠ 0 := by {
        intro z_1 hz_1
        have hnorm: Complex.abs (z_1 - z) > 0 := by {
          have rev_tri : Complex.abs (z_1 - z) ≥ |(Complex.abs z_1 - Complex.abs z)| := by exact AbsoluteValue.abs_abv_sub_le_abv_sub Complex.abs z_1 z -- reverse triangle inequality
          have hn : (Complex.abs z_1 - Complex.abs z) ≠ 0 := by {
            have hnaux : Complex.abs z_1 ≠  Complex.abs z := by {
              simp at hz_1
              simp at h
              linarith [hz_1, h]
            }
            exact sub_ne_zero_of_ne hnaux
          }
          have hn' : norm (Complex.abs z_1 - Complex.abs z) > 0 := by exact norm_pos_iff'.mpr hn
          exact gt_of_ge_of_gt rev_tri hn'
        }
        exact (AbsoluteValue.pos_iff Complex.abs).mp hnorm
        }
        let φ : ℂ → ℂ := fun z_1 ↦ z_1 - z
        have haux : Continuous φ := by exact _root_.continuous_sub_right z
        have haux' : ContinuousOn φ (closedBall 0 1) := by exact Continuous.continuousOn haux
        apply inverse_continuous_ball
        · exact haux'
        · exact fun s a ↦ hz_1 s a
      · intro z_1 hz_1
        simp at *
        apply inverse_differentiable_ball
        simp
        have hnorm: Complex.abs (z_1 - z) > 0 := by {
          have rev_tri : Complex.abs (z_1 - z) ≥ |(Complex.abs z_1 - Complex.abs z)| := by {
            exact AbsoluteValue.abs_abv_sub_le_abv_sub Complex.abs z_1 z
          } -- reverse triangle inequality
          have hn : (Complex.abs z_1 - Complex.abs z) ≠ 0 := by {
            have hnaux : Complex.abs z_1 ≠  Complex.abs z := by {
              linarith[hz_1, h]}
            exact sub_ne_zero_of_ne hnaux}
          have hn' : norm (Complex.abs z_1 - Complex.abs z) > 0 := by exact norm_pos_iff'.mpr hn
          exact gt_of_ge_of_gt rev_tri hn'
            }
        · intro s hs
          simp at hs
          have hnorm': Complex.abs (s - z) > 0 := by {
          have rev_tri : Complex.abs (s - z) ≥ |(Complex.abs s - Complex.abs z)| := by {
            exact AbsoluteValue.abs_abv_sub_le_abv_sub Complex.abs s z
          } -- reverse triangle inequality
          have hn : (Complex.abs s - Complex.abs z) ≠ 0 := by {
            have hnaux : Complex.abs s ≠  Complex.abs z := by {linarith[hs, h]}
            exact sub_ne_zero_of_ne hnaux}
          have hn' : norm (Complex.abs s - Complex.abs z) > 0 := by exact norm_pos_iff'.mpr hn
          exact gt_of_ge_of_gt rev_tri hn'}
          exact (AbsoluteValue.pos_iff Complex.abs).mp hnorm'
        simp
        linarith[hz_1]
      · linarith
    }
    simp[h₀]
}

-- DISCRETE WINDING NUMBER??
#check constant_of_derivWithin_zero
#check Continuous.deriv_integral
#check circleIntegral.integral_sub_inv_of_mem_ball
#check Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
