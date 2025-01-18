import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

/- In this document we present some basic definitions of the winding number around a point x
Intuitively, for an oriented closed curve γ, we can define it as

w(γ, x) = "number of times γ winds around x"

-/

/- To warm up, we will start with probably one of the most basic definitios of the winding number,
this is, using the Cauchy Integral Formula (from now on, CIF) -/


/- First definitions will be way simpler, but this will escalate quickly! -/

open Set unitInterval Finset Metric

structure curve where
 toFun : ℝ → ℂ
 class_c1 : ContDiff ℝ 1 toFun

 -- The aim of defining it on the whole ℝ is avoiding differentiability issues at the endpoints, but
 -- this does not afect to the definition of the curve at all. We can see it as a map from [0, 1] to ℂ,
 -- but it keeps winding again and again if we extend it to ℝ. This might not be trivial for simple curves,
 -- but it is for closed curves. We well give a more detailed explanation later.

-- It is sometimes useful to interpret curves as (ℝ → ℂ) maps
instance : CoeFun curve fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- We'll make continuity and differentiability of curves explicit using Lemmas

lemma curve.ContOn (γ : curve) : ContinuousOn γ I := by {
  have hcont : Continuous γ := γ.class_c1.continuous
  exact Continuous.continuousOn hcont
  }

lemma curve.Cont (γ : curve) : Continuous γ := by {
  exact γ.class_c1.continuous
  }

lemma curve.Diff (γ : curve) : Differentiable ℝ γ  := by {
  apply ContDiff.differentiable γ.class_c1
  simp
}

lemma curve.DiffOn (γ : curve) : DifferentiableOn ℝ γ I := by {
  exact Differentiable.differentiableOn $ curve.Diff γ
}

lemma curve.Cont_deriv (γ : curve) : Continuous (deriv γ) := by {
  apply ContDiff.continuous_deriv γ.class_c1
  simp
}

lemma curve.Cont_derivOn (γ : curve) : ContinuousOn (deriv γ) $ I := by {
  have hdiff : Continuous (deriv γ) := by {
    apply ContDiff.continuous_deriv γ.class_c1
    simp
  }
  exact Continuous.continuousOn hdiff
}
-- Let us now define the structure of a closed curve from the definition of curve. It inherits
-- continuity and differentiability

structure closed_curve extends curve where
closed : toFun 0 = toFun 1

-- Closed curves can also be seen as functions, as we've done before

instance : CoeFun (closed_curve) fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- Let us check this defintion works with the following example

def curve.is_closed {a b : ℝ} (γ : curve) : Prop :=
  γ.toFun a = γ.toFun b

lemma closed_curve.Cont (γ : closed_curve) : Continuous γ := by {
  exact curve.Cont γ.tocurve
  }

lemma closed_curve.ContOn (γ : closed_curve) : ContinuousOn γ I := by {
  exact curve.ContOn γ.tocurve
}

lemma closed_curve.Diff (γ : closed_curve) : Differentiable ℝ γ := by {
  exact curve.Diff γ.tocurve
}

lemma closed_curve.DiffOn (γ : closed_curve) : DifferentiableOn ℝ γ I := by {
  exact curve.DiffOn γ.tocurve
}

lemma closed_curve.Cont_deriv (γ : closed_curve) : Continuous (deriv γ) := by {
  apply ContDiff.continuous_deriv γ.class_c1
  simp
}
-- To generalize, we can define piecewise curves:

structure piecewiseCurve (n : ℕ) where
  curves : Fin n → curve

-- A curve can be seen as a 1-curve piecewise curve:

instance : Coe curve (piecewiseCurve 1) where
  coe := fun c => {curves := fun 0 => c}

/- Now, we define the concatenation of piecewise curves. If γ is a piecewise curve formed by n curves
 and ψ is a piecewise curve formed by m, the γψ is a piecewise curve with (n + m) curves -/


def concatenationOfCurves {n m : ℕ} (γ : piecewiseCurve n) (ψ : piecewiseCurve m) : piecewiseCurve (n + m) :=
  {curves := fun i => by
    by_cases h : i < n
    · exact γ.curves $ Fin.castLT i h
    · simp_all only [not_lt]
      refine ψ.curves $ Fin.subNat n {
        val := i
        isLt := ?_
      } h
      rw [add_comm m n]
      exact i.isLt
  }

def curve_reverse (γ : curve) : curve := {
  toFun := fun t => γ.toFun (1 - t)
  class_c1 := by {
    have heq : (fun t ↦ γ.toFun (1 - t)) = γ.toFun ∘ (λ t => 1 - t) := by {
      ext1 t
      simp
    }
    rw [heq]
    apply ContDiff.comp
    · exact γ.class_c1
    · have hf : ContDiff ℝ 1 (id : ℝ → ℝ) := by {
        refine contDiff_id
      }
      have ht : ContDiff ℝ 1 (λ (t : ℝ) => (1 : ℝ)) := by {
        refine contDiff_const
      }
      exact ContDiff.sub ht hf
  }
}

def closed_curve_reverse (γ : closed_curve) : closed_curve := {
  toFun := fun t => γ.toFun (1 - t)
  class_c1 := by {
    have heq : (fun t ↦ γ.toFun (1 - t)) = γ.toFun ∘ (λ t => 1 - t) := by {
      ext1 t
      simp
    }
    rw [heq]
    apply ContDiff.comp
    · exact γ.class_c1
    · have hf : ContDiff ℝ 1 (id : ℝ → ℝ) := by {
        refine contDiff_id
      }
      have ht : ContDiff ℝ 1 (λ (t : ℝ) => (1 : ℝ)) := by {
        refine contDiff_const
      }
      exact ContDiff.sub ht hf
  }
  closed := by {
    simp
    exact γ.closed.symm
  }
}

/- Anyways, we will potentially make use of closed_curves. The definition of piecewise curves is given
 in case we need it later -/

-- We give the first def of Winding Number

noncomputable def ω (z : ℂ) (γ : closed_curve) : ℂ :=
              1/(2*Real.pi*Complex.I) *  ∫ t in I, (deriv γ t) / (γ t - z)

-- Now we define the interior and exterior of a curve using the winding number (by a proven lemma, ω is always an integer)

def interiorOfClosedCurve (γ : closed_curve) : Set ℂ := {z : ℂ | ω z γ ≠ 0 ∧ z ∉ γ '' I}

def exteriorOfClosedCurve (γ : closed_curve) : Set ℂ := {z : ℂ | ω z γ = 0 ∧ z ∉ γ '' I}

-- For completeness we also include the definition for the image of a closed curve

def imageOfClosedCurve (γ : closed_curve) : Set ℂ := {z : ℂ | z ∈ γ '' I}

def CircleCurve_whole (γ : closed_curve) : Prop := (γ.toFun = (fun (θ : ℝ)  ↦ Complex.exp (2*π*Complex.I*θ)))

noncomputable def length (γ : curve) : ℝ := ∫ t in I, Complex.abs (deriv γ t)

noncomputable def integral_over_curve (γ : curve) (f : ℂ → ℂ) : ℂ := ∫ t in I, f (γ t) * deriv γ t

#min_imports
