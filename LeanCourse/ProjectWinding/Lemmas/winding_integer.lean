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
import Mathlib.Tactic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Function.L1Space
import LeanCourse.ProjectWinding.Definitions.curves

open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
--open scoped Real NNReal Interval Pointwise Topology
open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics
open Set unitInterval Finset Metric

noncomputable section

open Classical

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
theorem inverse_continuous_ball_2 (g : ℂ → ℂ)
(h : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ (g s)⁻¹) (closedBall 0 1) := by
{
  have hs0 : ∀ s ∈ closedBall 0 1, 1 / g s  = (g s)⁻¹ := by {
    norm_num
  }
  have heq : ContinuousOn (fun s ↦ 1 / (g s)) (closedBall 0 1) ↔ ContinuousOn (fun s ↦ (g s)⁻¹) (closedBall 0 1) := by exact continuousOn_congr hs0
  rw[← heq]
  exact inverse_continuous_ball g h h_v
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
theorem inverse_differentiable_ball_2 (g : ℂ → ℂ)
(h : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ (g s)⁻¹) s  := by {
  intro s hs
  exact DifferentiableAt.inv (h s hs) (h_v s hs)
}

lemma ftc (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

lemma ftc_2 (f : ℝ → ℂ) (hf : ContinuousOn f (I)) :
      ∀ b ∈ I, deriv (fun u ↦ ∫ x : ℝ in (0)..u, f x) b = f b :=
  by {
    intro b hb
    have h_deriv : HasDerivAt (fun u ↦ ∫ x : ℝ in (0)..u, f x) (f b) b := by {
      have hint : IntervalIntegrable f volume (0) b := by {
        have hI : [[0, b]] ⊆ I := by {
          intro x hx
          obtain ⟨h1, h2⟩ := hx
          simp at *
          obtain ⟨h3, h4⟩ := hb
          obtain hP|hQ := h1
          · obtain h5|h6 := h2
            · have hxx : x ≤ 1 := by exact le_implies_le_of_le_of_le h5 h4 h3
              exact ⟨hP, hxx⟩
            · have hxx : x ≤ 1 := by exact Preorder.le_trans x b 1 h6 h4
              exact ⟨hP, hxx⟩
          · obtain h5|h6 := h2
            · have hxx : 0 ≤ x := by exact Preorder.le_trans 0 b x h3 hQ
              have hxxx : x = 0 := by exact le_antisymm h5 hxx
              rw [hxxx] at hQ
              have hb0 : b = 0 := by exact le_antisymm hQ h3
              have hx1 : x ≤ 1 := by linarith
              exact ⟨hxx, hx1⟩
            · have hxx : 0 ≤ x := by exact Preorder.le_trans 0 b x h3 hQ
              have hx1 : x ≤ 1 := by linarith
              exact ⟨hxx, hx1⟩
        }
        have haux : ContinuousOn f (Set.uIcc 0 b) := by exact ContinuousOn.mono hf hI
        exact ContinuousOn.intervalIntegrable haux
      }
      have hbb : ContinuousAt f b := by {
        sorry
      }
      have hmeas : StronglyMeasurableAtFilter f (nhds b) := by {
        sorry
      }
      exact intervalIntegral.integral_hasDerivAt_right hint hmeas hbb
    }
    exact HasDerivAt.deriv h_deriv
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
          · exact h₁
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
    have h_cont : ContinuousOn (fun t ↦ deriv γ.toFun t / (γ.toFun t - z)) I := by exact h_cont
    have hcont : ContinuousOn ψ I := by {
      refine ContinuousOn.mul ?_ ?_
      · have hF : ContinuousOn (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) I := by {
        apply ContinuousOn.neg
        have h_int : IntegrableOn (fun t ↦ deriv γ.toFun t / (γ.toFun t - z)) I := by {
          have hK : IsCompact I := by exact isCompact_Icc
          exact ContinuousOn.integrableOn_compact hK h_cont
        }
        have hI : Set.uIcc 0 1 = I := by {
          refine uIcc_of_le ?h; linarith
        }
        rw [← hI] at h_int
        rw [← hI]
        exact intervalIntegral.continuousOn_primitive_interval h_int
        }
        exact ContinuousOn.cexp hF
      · exact ContinuousOn.sub hγ (continuousOn_const)
    }
    have hderiv : ∀ t ∈ Set.Ico 0 1, HasDerivWithinAt ψ 0 (Set.Ici t) t := by {
      intro t ht
      have htt : t ∈ I := by exact mem_Icc_of_Ico ht
      have h_deriv : deriv ψ t = 0 := deriv₀ t htt
      /-have h_tendsto : Filter.Tendsto (λ x => (ψ x - ψ t) / (x - t)) (𝓝[Set.Ici t \ {t}] t) (𝓝 0) := by {
        sorry
     }-/
      --rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      specialize deriv₀ t htt
      have hmini : HasDerivAt ψ (deriv ψ t) t := by {
        rw [hasDerivAt_iff_tendsto]
        rw [deriv₀]
        simp [mul_zero]
        have eq1 : (fun x' ↦ |x' - t|⁻¹ * Complex.abs (ψ x' - ψ t))
        = (fun x' ↦ Complex.abs (ψ x' - ψ t) * |x' - t|⁻¹) := by {
          ext1 x
          exact CommMonoid.mul_comm |x - t|⁻¹ $ Complex.abs (ψ x - ψ t)
        }
        have eq2 : (fun x' ↦ |x' - t|⁻¹ * Complex.abs (ψ x' - ψ t))
        = (fun x' ↦ Complex.abs (ψ x' - ψ t) / |x' - t|) := by {
          exact eq1
        }
        rw [eq2]
        have hnorm : (fun x => Complex.abs (ψ x - ψ t) / |x - t|) =
        (fun x => Complex.abs ((ψ x - ψ t) / (x- t))) := by {
          ext1 x
          field_simp
          have hn : |x - t| = Complex.abs (x - t) := by {
            have hco : (↑x - ↑t) = ↑(x - t) := by exact rfl
            rw [hco]
            rw [← Complex.abs_ofReal]
            rw [Complex.ofReal_sub]
          }
          rw [hn]
        }
        rw [hnorm]
        simp
        have habs : (fun x ↦ Complex.abs ((ψ x - ψ t) / (↑x - ↑t))) =
        (fun x ↦ ‖(ψ x - ψ t) / (↑x - ↑t)‖) := by {
          ext1 x
          exact rfl
        }
        have hcom : (fun x ↦ Complex.abs ((ψ x - ψ t) / (↑x - ↑t))) =
        (fun x ↦ Complex.abs (ψ x - ψ t) / Complex.abs (↑x - ↑t)) := by {
          ext1 x
          simp_all only [Set.mem_Icc, ne_eq, and_imp, Set.mem_Ico, true_and, map_div₀, norm_div, Complex.norm_eq_abs,
            g', h', φ, g, ψ]
        }
        rw [← hcom, habs]
        --rw [tendsto_zero_iff_norm_tendsto_zero]
        have h_inner : Tendsto (fun x ↦ (ψ x - ψ t) / (↑x - ↑t)) (𝓝 t) (𝓝 0) := by {
          rw [← dslope_same ψ t] at h_deriv
          have eqaux : (fun x ↦ (ψ x - ψ t) / (x - t)) = (fun x => (ψ x - ψ t) * (x - t)⁻¹) := by {
            ext1 x
            rw [div_eq_mul_inv]
            congr
            simp_all only [Set.mem_Icc, ne_eq, and_imp, Set.mem_Ico, true_and, dslope_same,
            map_div₀, ofReal_inv,
              Complex.ofReal_sub, g', h', φ, g, ψ]
          }
          have eqaux1 : (fun x ↦ (ψ x - ψ t) * (x - t)⁻¹) = (fun x => (x - t)⁻¹ * (ψ x - ψ t)) := by {
            ext1 x
            exact CommMonoid.mul_comm (ψ x - ψ t) ↑(x - t)⁻¹
          }
          rw [eqaux, eqaux1]
          have dot : (fun x ↦ ↑(x - t)⁻¹ * (ψ x - ψ t)) = (fun x ↦ ↑(x - t)⁻¹ • (ψ x - ψ t)) := by {
            simp
          }
          rw [dot]

          sorry
        }
        rw [tendsto_zero_iff_norm_tendsto_zero] at h_inner
        exact h_inner
      }
      rw [deriv₀] at hmini
      exact HasDerivAt.hasDerivWithinAt hmini
    }
    have h_const : ∀ x ∈ Set.Icc 0 1, ψ x = ψ 0 := by {
      intro x hx
      exact constant_of_has_deriv_right_zero hcont hderiv x hx
    }
    simp_all only [Set.mem_Icc, ne_eq, and_imp, intervalIntegral.integral_same,
    neg_zero, Complex.exp_zero, one_mul,
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

/- We want to evaluate the values of ω when γ is the unit circle. In Mathlib, there are some lemmas which help
    to solve this. However, they are based on the structure CircleMap.
-/

-- For this reason, we first show the following useful equality:

lemma contour_integral_eq_curve_integral (γ : closed_curve) (h_circle : CircleCurve_whole γ) (z : ℂ ):
∫ (t : ℝ) in I, deriv γ t / (γ t - z) = ∮ (z_1 : ℂ) in C(0, 1), (z_1 - z)⁻¹ := by {
    rw[circleIntegral_def_Icc]
    unfold circleMap
    simp
    have h_circle_1 : ∀ θ ∈ I, γ θ = Complex.exp (2*π*Complex.I * θ) := by {
      intro t
      rw[h_circle]
      simp
    }
    have h_circle_2 : ∀ θ ∈ I, γ θ = Complex.exp (Complex.I*2*π*θ) := by {
      intro θ hθ
      specialize h_circle_1 θ hθ
      norm_num[h_circle_1]
      ring_nf
    }
    have hsubs : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∫ (t : ℝ) in I, deriv γ.toFun t / (cexp («I» * 2 * ↑π * ↑t) - z) := by {
      refine setIntegral_congr_ae₀ ?hs ?h -- should be easy to show
      · exact nullMeasurableSet_Icc
      · have haux : ∀ x ∈ I, deriv γ.toFun x / (γ.toFun x - z) = deriv γ.toFun x / (cexp («I» * 2 * ↑π * ↑x) - z) := by
          exact fun x a ↦ congrArg (HDiv.hDiv (deriv γ.toFun x)) (congrFun (congrArg HSub.hSub (h_circle_2 x a)) z)
        exact ae_of_all volume haux
    }
    rw[hsubs]
    have h_all : ∀ (x:ℝ) (y : ℂ), HasDerivAt (fun (x : ℝ)  ↦ cexp (x*y)) (y * cexp (x*y)) x := by {
        intro x y
        let h₁ : ℝ → ℂ := (fun x ↦ (x : ℂ) *y)
        let e : ℂ → ℂ := (fun x ↦ x*y)
        let h₂ : ℂ → ℂ := (fun z ↦ cexp z)
        have h : HasDerivAt e y (x : ℂ) := by exact hasDerivAt_mul_const y
        have h' : HasDerivAt h₁ y x := by exact HasDerivAt.comp_ofReal (e := e) (e' := y) (hf := h) -- By hint
        have hh2 : HasDerivAt h₂ (cexp (h₁ x)) (h₁ x) := by exact Complex.hasDerivAt_exp (h₁ x)
        have hder : HasDerivAt (h₂ ∘ h₁) (cexp (h₁ x) * y ) x := by exact HasDerivAt.comp x hh2 h'
        have hxy : x * y = h₁ x := by exact rfl
        rw[hxy]
        have h1h2 : (fun (x : ℝ)  ↦ cexp (x * y)) = h₂ ∘ h₁ := by exact rfl
        rw[h1h2]
        rw[mul_comm]
        exact hder
      }
    have h_deriv_1 : ∀ θ ∈ Set.Icc 0 (2*π), HasDerivAt (fun (θ : ℝ)  ↦ cexp (↑θ * «I»)) (Complex.I * cexp (↑θ * «I»)) θ := by {
      intro θ hθ
      specialize h_all θ Complex.I
      exact h_all
    }
    have h_deriv_1' : ∀ θ ∈ Set.Icc 0 (2*π), deriv (fun θ ↦ cexp (↑θ * «I»)) θ = Complex.I * cexp (↑θ * «I») := by {
      intro θ hθ
      specialize h_deriv_1 θ hθ
      exact HasDerivAt.deriv h_deriv_1
    }
    have h_deriv_1'' : ∀ θ ∈ Set.Icc 0 (2*π), deriv (fun θ ↦ cexp (↑θ * «I»)) θ * ((cexp (↑θ * «I»)) - z)⁻¹
    = Complex.I * cexp (↑θ * «I») * ((cexp (↑θ * «I»)) - z)⁻¹ := by {
      intro θ hθ
      specialize h_deriv_1' θ hθ
      rw[h_deriv_1']
    }
    have hI : I = Set.Icc 0 1 := by exact rfl
    have h_deriv_2 : ∀ t : ℝ, HasDerivAt (fun t ↦ γ.toFun t) ((«I» * 2 * ↑π ) * cexp («I» * 2 * ↑π * ↑t)) t := by {
      intro t
      specialize h_all t («I» * 2 * ↑π )
      rw[h_circle]
      simp
      have haux : ∀ t : ℝ, 2 * ↑π * «I» * ↑t = ↑t * («I» * 2 * ↑π) := by {
        intro t
        ring
      }
      have haux' : (fun (t : ℝ ) ↦ cexp (2 * ↑π * «I» * ↑t)) = (fun (x : ℝ ) ↦ cexp (↑x * («I» * 2 * ↑π))) := by {
        ext t
        specialize haux t
        rw[haux]
      }
      repeat rw[haux']
      have haux'' : ∀ t : ℝ, (↑t * («I» * 2 * ↑π)) = («I» * 2 * ↑π * ↑t) := by {
        intro t
        ring
      }
      exact  HasDerivAt.congr_deriv h_all (congrArg (HMul.hMul («I» * 2 * ↑π)) (congrArg cexp (haux'' t)))
      }
    have h_deriv2 : ∀ t ∈ I, HasDerivAt (fun t ↦ γ.toFun t) ((«I» * 2 * ↑π ) * cexp («I» * 2 * ↑π * ↑t)) t := by exact fun t a ↦ h_deriv_2 t
    have h_deriv_2': ∀ t ∈ I, deriv (fun t ↦ γ.toFun t) t = ((«I» * 2 * ↑π ) * cexp («I» * 2 * ↑π * ↑t)) := by {
        intro t ht
        specialize h_deriv2 t ht
        exact HasDerivAt.deriv h_deriv2
    }
    have h_deriv_2'' : ∀ t ∈ I, deriv (fun t ↦ γ.toFun t) t / (cexp («I» * 2 * ↑π * ↑t) - z) = ((«I» * 2 * ↑π ) * cexp («I» * 2 * ↑π * ↑t)) / ((cexp («I» * 2 * ↑π * ↑t) - z)) := by {
      exact fun t a ↦ congrFun (congrArg HDiv.hDiv (h_deriv_2' t a)) (cexp («I» * 2 * ↑π * ↑t) - z)
    }
    have hmeasur : MeasurableSet (Set.Icc 0 (2*π)) := by measurability
    have hmeasI : MeasurableSet I := by measurability

    have h_int_eq_1 :  ∫ (θ : ℝ) in Set.Icc 0 (2 * π), deriv (fun θ ↦ cexp (↑θ * «I»)) θ * ((cexp (↑θ * «I»)) - z)⁻¹
    = ∫ (θ : ℝ) in Set.Icc 0 (2 * π), (Complex.I * cexp (↑θ * «I»)) * ((cexp (↑θ * «I»)) - z)⁻¹ := by {
      exact setIntegral_congr hmeasur h_deriv_1''
    }
    have h_int_eq_2 : ∫ (t : ℝ) in I, deriv γ.toFun t / (cexp («I» * 2 * ↑π * ↑t) - z) = ∫ (t : ℝ) in I, ((«I» * 2 * ↑π ) * cexp («I» * 2 * ↑π * ↑t)) / ((cexp («I» * 2 * ↑π * ↑t) - z)) := by {
      exact setIntegral_congr hmeasI h_deriv_2''
    }
    rw[h_int_eq_1, h_int_eq_2]
    field_simp
    -- All left is to do a change of variables.
    let f : ℝ → ℝ := fun x ↦ (2*π)*x

    have hf₁ : InjOn f I := by {
      unfold InjOn
      intro x hx y hy
      simp_rw[f]
      intro hexp
      have hpos : 2 * π ≠ 0 := by {
        simp
        exact pi_ne_zero
      }
      field_simp[hpos] at hexp
      assumption
    }
    let f' : ℝ → ℝ := fun x ↦ 2*π
    have hf' : ∀ x ∈ I, HasDerivWithinAt f (f' x) I x := by {
      have hf'' : ∀ x : ℝ, HasDerivAt f (f' x) x := by {
        intro x
        simp_rw[f, f']
        -- We state the following lemma to use hasDerivAt.mul_const
        have htrivial : (fun x ↦ 2 * π * x) =  (fun x ↦ x * (2*π )):= by {
          ext x
          ring
        }
        rw[htrivial]
        exact hasDerivAt_mul_const (2 * π)
      }
      exact fun x a ↦ HasDerivAt.hasDerivWithinAt (hf'' x)
    }
    let g₁ : ℝ → ℂ := fun θ ↦ «I» * cexp (↑θ * «I») / (cexp (↑θ * «I») - z)
    have hfeq : f '' I = Set.Icc 0 (2*π) := by {
      ext y
      constructor
      · intro a₁
        simp_all only [Set.mem_Icc, and_imp, implies_true, measurableSet_Icc, Set.mem_image, f, f']
        obtain ⟨w, h⟩ := a₁
        obtain ⟨left, right⟩ := h
        obtain ⟨left, right_1⟩ := left
        subst right
        apply And.intro
        · positivity
        · field_simp
          assumption
      · intro hy₁
        simp
        use (y/(2*π))
        have hpospi : (1 / 2*π) ≥ 0 := by {
              have h' : π ≥ 0 := by exact pi_nonneg
              have h'' : 2*π ≥ 0 := by linarith
              field_simp[h', h'']
              linarith
            }
        apply And.intro
        · apply And.intro
          · have hy₂ : y ≥ 0 := by {
            simp at hy₁
            linarith}
            have hrepl : y / (2*π ) = y * (1/(2*π )) := by exact div_eq_mul_one_div y (2 * π)
            rw[hrepl]
            refine Right.mul_nonneg hy₂ ?h.left.left.hb
            positivity
          · simp at hy₁
            obtain ⟨h1, h2⟩ := hy₁
            have hrepl : y / (2*π ) = y * (1/(2*π )) := by exact div_eq_mul_one_div y (2 * π)
            rw[hrepl]
            calc
            y * (1/ (2*π )) ≤ 2*π * (1/ (2*π )) := by {
              refine mul_le_mul_of_nonneg_right h2 ?a0
              positivity
            }
            _= 1 := by field_simp
        · simp_rw[f]
          field_simp
    }
    rw[← hfeq]
    apply Eq.symm
    have hinteq : ∫ (θ : ℝ) in f '' I, «I» * cexp (↑θ * «I») / (cexp (↑θ * «I») - z) = ∫ (θ : ℝ) in f '' I, g₁ θ := by norm_num -- should be easy
    rw[hinteq]
    simp[integral_image_eq_integral_abs_deriv_smul (f := f) (f' := f') (hf := hf₁) (hf' := hf') (g := g₁)]
    simp_rw[f, g₁, f']
    have hpipos : |2 * π| = 2 * π := by {
      have hpos : 2*π ≥ 0 := by positivity
      exact _root_.abs_of_nonneg hpos
      }
    rw[hpipos]
    simp
    have h₀int : ∀ t : ℝ, 2 * ↑π * («I» * cexp (2 * ↑π * ↑t * «I») / (cexp (2 * ↑π * ↑t * «I») - z)) = «I» * 2 * ↑π * cexp («I» * 2 * ↑π * ↑t) / (cexp («I» * 2 * ↑π * ↑t) - z) := by {
      intro t
      ring_nf
    }
    exact setIntegral_congr hmeasI fun ⦃x⦄ a ↦ h₀int x
    }

-- Actually, we only need for the curve to coincide with the circle in [0,1], by our definition of Winding Number

lemma contour_integral_eq_curve_integral_strong (γ : closed_curve) (h_circle : ∀ t ∈ I, γ t = Complex.exp (Complex.I * 2*π* t)) (z : ℂ ):
∫ (t : ℝ) in I, deriv γ t / (γ t - z) = ∮ (z_1 : ℂ) in C(0, 1), (z_1 - z)⁻¹ := by {
  let g : ℝ → ℂ := fun (θ : ℝ) ↦ Complex.exp (2*π*Complex.I*θ)
  have gdiff : Differentiable ℝ g := by {
    refine Differentiable.cexp ?hc
    have hdif : Differentiable ℝ (fun (θ : ℝ) ↦ (θ : ℂ)) := by {
      have hderiv : ∀ (θ : ℝ), HasDerivAt (fun (θ : ℝ) ↦ (θ : ℂ)) 1 θ := by {
        intro θ
        apply HasDerivAt.comp_ofReal (e := fun θ ↦ θ) (e' := 1)
        exact hasDerivAt_id' (θ : ℂ)
      }
      intro θ
      specialize hderiv θ
      exact HasFDerivAt.differentiableAt hderiv
    }
    fun_prop
  }
  have gdiff' : DifferentiableOn ℝ g I := by exact Differentiable.differentiableOn gdiff
  have deriv_aux_g : ∀ (θ :ℝ), HasDerivAt (fun (θ : ℝ) ↦ Complex.exp (2*π*Complex.I*θ)) ((2*π*Complex.I)*Complex.exp (2*π*Complex.I*θ)) θ := by {
    intro θ
    let e : ℂ → ℂ := fun (θ : ℂ) ↦ Complex.exp (2*π*Complex.I*θ)
    have h_all : ∀ (x:ℝ) (y : ℂ), HasDerivAt (fun (x : ℝ)  ↦ cexp (x*y)) (y * cexp (x*y)) x := by {
        intro x y
        let h₁ : ℝ → ℂ := (fun x ↦ (x : ℂ) *y)
        let e : ℂ → ℂ := (fun x ↦ x*y)
        let h₂ : ℂ → ℂ := (fun z ↦ cexp z)
        have h : HasDerivAt e y (x : ℂ) := by exact hasDerivAt_mul_const y
        have h' : HasDerivAt h₁ y x := by exact HasDerivAt.comp_ofReal (e := e) (e' := y) (hf := h) -- By hint
        have hh2 : HasDerivAt h₂ (cexp (h₁ x)) (h₁ x) := by exact Complex.hasDerivAt_exp (h₁ x)
        have hder : HasDerivAt (h₂ ∘ h₁) (cexp (h₁ x) * y ) x := by exact HasDerivAt.comp x hh2 h'
        have hxy : x * y = h₁ x := by exact rfl
        rw[hxy]
        have h1h2 : (fun (x : ℝ)  ↦ cexp (x * y)) = h₂ ∘ h₁ := by exact rfl
        rw[h1h2]
        rw[mul_comm]
        exact hder
      }
    have h_all' : ∀ (x : ℝ) (y : ℂ), HasDerivAt (fun (x : ℝ)  ↦ cexp (y * (x : ℂ ))) (y * cexp (y * (x : ℂ ))) x := by {
      intro x y
      specialize h_all x y
      have hcomm : (x : ℂ ) * y = y * (x : ℂ ) := by ring
      simp_rw[hcomm] at h_all
      have hcomm' : (fun (x :ℝ) ↦ cexp (↑x * y)) = (fun (x : ℝ) ↦ cexp (y * ↑x)) := by {
        ext a
        ring_nf
      }
      simp_rw[← hcomm']
      exact h_all
    }
    specialize h_all' θ (2 * ↑π * «I» )
    exact h_all'
  }
  have deriv_g : deriv g = fun (θ : ℝ) ↦ (2*π*Complex.I) *Complex.exp (2*π*Complex.I*θ) := by {
    exact deriv_eq deriv_aux_g
  }
  have g'cont : ContinuousOn (deriv g) $ I := by {
    simp_rw[deriv_g]
    fun_prop
  }
  have g0g1 : g 0 = g 1 := by {
    simp_rw[g]
    norm_num
  }
  let g₁ : closed_curve := {toFun := g, diff_curve := gdiff', cont_deriv := g'cont, closed := g0g1}
  have h_coinc : ∀ x ∈ Set.Ioo (0 : ℝ) 1, γ.toFun x = g₁.toFun x := by {
    intro x hx
    simp_rw[g]
    have hxop : x ∈ I := by exact mem_Icc_of_Ioo hx
    specialize h_circle x hxop
    rw[h_circle]
    ring_nf
  }
  have h_deriv_coinc_aux : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv γ.toFun x = deriv g₁.toFun x  := by {
    intro x hx
    refine EventuallyEq.deriv_eq ?hL
    have hneigh : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x := by {
      refine IsOpen.mem_nhds ?hs hx
      exact isOpen_Ioo
    }
    exact eventuallyEq_of_mem hneigh h_coinc
  }
  have h_deriv_coinc : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv γ.toFun x / (γ.toFun x - z) = deriv g₁.toFun x / (g₁.toFun x - z) := by {
    intro x hx
    exact
      Mathlib.Tactic.LinearCombination'.div_pf (h_deriv_coinc_aux x hx)
        (congrFun (congrArg HSub.hSub (h_coinc x hx)) z)
  }
  have hmeasIop : MeasurableSet (Set.Ioo (0 : ℝ)  1) := by measurability
  have hinteq : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∫ (t : ℝ) in I, deriv g₁.toFun t / (g₁.toFun t - z) := by {
    simp_rw [@integral_Icc_eq_integral_Ioo]
    exact setIntegral_congr hmeasIop h_deriv_coinc
  }
  rw[hinteq]
  exact contour_integral_eq_curve_integral g₁ rfl z
}

#check Set.Icc 0 (2*π)

#check set_integral_congr_ae₀
#check MeasureTheory.setIntegral_congr_ae₀
#check integral_image_eq_integral_abs_deriv_smul
#check mul_comm

lemma winding_circle_inside (γ : closed_curve) (h_circle : ∀ t ∈ I, γ t = Complex.exp (Complex.I * 2*π* t)) (z : ℂ ) (h : norm z < 1) : ω z γ = 1 := by {
  unfold ω
  have h_int : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = 2*π*Complex.I := by {
    let const : ℂ → ℂ := fun z ↦ 1
    have integ_eq : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∮ (z_1 : ℂ) in C(0, 1), (z_1 - z)⁻¹ := by {
      exact contour_integral_eq_curve_integral_strong γ h_circle z
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

  lemma winding_circle_outside (γ : closed_curve) (h_circle : ∀ t ∈ I, γ t = Complex.exp (Complex.I * 2*π* t))
  (z : ℂ ) (h : norm z > 1) : ω z γ = 0 := by {
    unfold ω
    have h₀ : ∫ (t : ℝ) in I, deriv γ t / (γ t - z) = 0 := by {
      let g : ℂ → ℂ := fun z_1 ↦ 1 / (z_1 - z)
      have h_1 : ∫ (t : ℝ) in I, deriv γ t / (γ t - z) = ∮ (z_1 : ℂ) in C(0, 1),
      (fun (z_1 : ℂ)  ↦ (z_1 - z)⁻¹) z_1 := by {
        exact contour_integral_eq_curve_integral_strong γ h_circle z}
      rw[h_1]
      apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        (f := fun (z_1 : ℂ)  ↦ (z_1 - z)⁻¹ ) (s := ∅)
      · exact countable_empty
      · have hz_1 : ∀ z_1 ∈ (closedBall 0 1), z_1 - z ≠ 0 := by {
        intro z_1 hz_1
        have hnorm: Complex.abs (z_1 - z) > 0 := by {
          have rev_tri : Complex.abs (z_1 - z) ≥ |(Complex.abs z_1 - Complex.abs z)| := by
           exact AbsoluteValue.abs_abv_sub_le_abv_sub Complex.abs z_1 z -- reverse triangle inequality
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
        apply inverse_continuous_ball_2
        · exact haux'
        · exact fun s a ↦ hz_1 s a
      · intro z_1 hz_1
        simp at *
        apply inverse_differentiable_ball_2
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
-- Next?

-- DISCRETE WINDING NUMBER??
#check constant_of_derivWithin_zero
#check Continuous.deriv_integral
#check circleIntegral.integral_sub_inv_of_mem_ball
#check Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
