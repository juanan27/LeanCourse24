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

open DifferentiableOn Finset
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
 class_c1 : ContDiffOn ℝ 1 toFun I

-- It is sometimes useful to interpret curves as (ℝ → ℂ) maps
instance : CoeFun curve fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- We'll make continuity and differentiability of curves explicit using Lemmas

lemma curve.ContOn (γ : curve) : ContinuousOn γ I := by {
  exact ContDiffOn.continuousOn γ.class_c1
  }


lemma curve.DiffOn (γ : curve) : DifferentiableOn ℝ γ I := by {
  apply ContDiffOn.differentiableOn γ.class_c1
  simp


}
lemma curve.Cont_derivOn (γ : curve) : ContinuousOn (deriv γ) $ I := by {
  sorry

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

-- To generalize, we can define piecewise curves:

structure piecewiseCurve (n : ℕ) where
  curves : Fin n → curve

-- A curve can be seen as a 1-curve piecewise curve:

instance : Coe curve (piecewiseCurve 1) where
  coe := fun c => {curves := fun 0 => c}

-- Now, we define the concatenation of piecewise curves. If γ is a piecewise curve formed by n curves
-- and ψ is a piecewise curve formed by m, the γψ is a piecewise curve with (n + m) curves

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

-- Anyways, we will potentially make use of closed_curves. The definition of piecewise curves is given
-- in case we need it later

noncomputable section

open Classical

-- We give the first def of Winding Number (HAVE TO REFINE THIS)
noncomputable def ω (z : ℂ) (γ : closed_curve) : ℂ :=
              1/(2*Real.pi*Complex.I) * ∫ t in I, (deriv γ t) / (γ t - z)


-- TO DO: DEMOSTRAR CON ESTA DEFINICION QUE ES UN ENTERO

-- HAY QUE TRABAJAR EN ESTA PRUEBA; DEFINIR ARGUMENTO (PPAL?)?

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
sorry
}

-- We prove now that the winding number is always an integer.

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
  have hg'' : ∀ t ∈ I , deriv g t = (deriv γ t) / (γ t - z) := by {
  intro t ht
  sorry
  }
  sorry
}
-- DISCRETE WINDING NUMBER??
