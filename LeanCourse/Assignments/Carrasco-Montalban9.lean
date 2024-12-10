import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by {
  sorry
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  sorry
  }


section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
#leansearch "intermediate_value_uIcc."
#leansearch "u_Icc_of_le."
#leansearch "mem_uIcc."
lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  unfold Injective at *
  by_contra h

  }

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  sorry
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  -- sorry
  by_contra h
  simp [not_or, StrictMono, StrictAnti] at h
  obtain ⟨⟨a, b, hab, h2ab⟩, ⟨c, d, hcd, h2cd⟩⟩ := h
  have h3cd : f c < f d := h2cd.lt_of_ne (h2f.ne hcd.ne)
  have h1 : a < c
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f hcd.le h3cd h (h.trans hab.le) hab |>.not_le h2ab
  have h2 : f c ≤ f a
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f h1.le h left_mem_Ici hab.le hab |>.not_le h2ab
  exact this hcd.le h3cd (h1.le.trans hcd.le) hcd.le h1 |>.not_le h2
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    sorry
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    sorry
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  sorry
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  sorry
  }
  -- sorry
  have h5 := h.derivWithin h3
  rw [← h.derivWithin h4, h1.derivWithin h3, h2.derivWithin h4] at h5
  norm_num at h5
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  unfold Injective at *
  by_contra h
  simp at h
  have h₀: [[f x, f a]] ⊆ f '' [[x, a]] := by {
    exact intermediate_value_uIcc (by exact Continuous.continuousOn hf)
  }
  have h₁: [[f a, f b]] ⊆ f '' [[a, b]] := by {
    exact intermediate_value_uIcc (by exact Continuous.continuousOn hf)
  }
  have h₂: [[f x, f b]] ⊆ f '' [[x, b]] := by {
    exact intermediate_value_uIcc (by exact Continuous.continuousOn hf)
  }
  by_cases hb : x ≥ b
  . have h₄: ∃ c, f a < c ∧ c < f b := by exact exists_between h2ab
    obtain ⟨c, h₄', h₄''⟩ := h₄
    have h₅: c ∈ [[f a, f b]] := by {
      rw [mem_uIcc]
      left
      constructor
      · exact le_of_lt h₄'
      · exact le_of_lt h₄''
    }
    specialize h₁ h₅
    have h₆: c ∈ [[f x, f b]] := by {
      rw [mem_uIcc]
      left
      constructor
      map_tacs [exact le_of_lt $ gt_trans h₄' h; exact le_of_lt h₄'']
    }
    specialize h₂ h₆
    have h₇: (f '' [[a, b]]) ∩ (f '' [[x, b]]) = {f b} := by {
      rw [Eq.symm (image_inter h2f)]
      have heq: [[a, b]] ∩ [[x, b]] = {b}:= by{
        rw [uIcc_of_le, uIcc_of_ge, Set.Icc_inter_Icc_eq_singleton]
        map_tacs [exact hab; exact hb; exact hb; exact hab]
      }
      simp[congrArg (image f) heq]
    }
    have h₈ : c ∈ f '' [[a, b]] ∩ f '' [[x, b]] := by exact mem_inter h₁ h₂
    rw [h₇] at h₈
    have h₉ := h2f $ h2f (congrArg f (congrArg f h₈))
    have h₁₀ : c ≥ f b := by exact le_of_eq $ h2f (h2f (congrArg f (congrArg f (id (Eq.symm h₉)))))
    subst h₉
    simp_all only [uIcc_of_ge, ge_iff_le, uIcc_of_le, lt_self_iff_false]
  . simp at hb
    have h₁₁ : ∃ c, f x < c ∧ c < f a := by exact exists_between h
    obtain ⟨c, h₁₁', h₁₁''⟩ := h₁₁
    have h₁₂ : c ∈ [[f x, f a]] := by {
      rw [mem_uIcc]
      left
      constructor
      map_tacs[exact le_of_lt h₁₁'; exact le_of_lt h₁₁'']
    }
    specialize h₀ h₁₂
    have h₁₃: c ∈ [[f x, f b]] := by {
      rw [mem_uIcc]
      left
      constructor
      map_tacs[exact le_of_lt h₁₁'; exact le_of_lt (gt_trans h2ab h₁₁'')]
    }
    specialize h₂ h₁₃
    have h₁₄: (f '' [[a, x]]) ∩ (f '' [[x, b]]) = {f x} := by {
      rw[Eq.symm $ image_inter h2f]
      have h₁₄': [[a, x]] ∩ [[x, b]] = {x} := by {
        rw [uIcc_of_le, uIcc_of_le, Set.Icc_inter_Icc_eq_singleton]
        map_tacs [exact hx; exact le_of_lt hb; exact le_of_lt hb; exact hx]
      }
      simp_all
    }
    have h₁₅: c ∈ f '' [[a, x]] ∩ f '' [[x, b]] := by {
      rw [uIcc_comm a x]
      exact mem_inter h₀ h₂
    }
    simp_all
  }


/- Prove the following using the change of variables theorem. -/
  lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
    -- the idea is to use integral_image_eq_integral_abs_deriv_smul. For this we shall make the following preparations:
    let g : ℝ → ℝ := fun x ↦ cos x
    let g' : ℝ → ℝ := fun x ↦ -sin x
    have hg': ∀ x ∈ [[0,π]], HasDerivWithinAt g (-sin x) [[0,π]] x := by {
      intro x₀ hx₀
      refine HasDerivAt.hasDerivWithinAt $ hasDerivAt_cos x₀
    }
    have injg : InjOn g (Icc 0 π) := by exact injOn_cos
    have hs : MeasurableSet [[0,π]] := by exact measurableSet_uIcc
    simp_all only [g]
    calc ∫ x in (0)..π, sin x * f (cos x) = ∫ x in [[0, π]], sin x * f (cos x) := by {
      rw [intervalIntegral.integral_of_le]
      have h': [[0, π]] = Icc 0 π := by refine uIcc_of_le ?h; exact pi_nonneg
      simp[h']
      map_tacs [exact Eq.symm integral_Icc_eq_integral_Ioc; exact pi_nonneg]
    }
    _= ∫ x in [[0, π]], (abs (sin x)) * f (cos x) := by {
      have h₀ :  ∀ x ∈ [[0, π]], sin x ≥ 0 := by {
        intro x hx
        rw[@mem_uIcc] at hx
        obtain hP|hQ := hx
        apply sin_nonneg_of_nonneg_of_le_pi
        · obtain ⟨hP', hP''⟩ := hP
          exact hP'
        · obtain ⟨hP', hP''⟩ := hP
          exact hP''
        · obtain ⟨hQ', hQ''⟩ := hQ
          have := calc
            0 < π := pi_pos
            _≤ 0 := Preorder.le_trans π x 0 hQ' hQ''
          linarith
      }
      have heq : ∀ x ∈ [[0, π]], sin x = |sin x|  := by {
        exact fun x a ↦ Eq.symm $ abs_of_nonneg (h₀ x a)
      }
      apply setIntegral_congr measurableSet_Icc
      intro y hy
      exact congrFun (congrArg HMul.hMul (heq y hy)) $ f (cos y)
    }
    _= ∫ x in (cos '' [[0,π]]), f x := by {
        rw[← uIcc_of_le] at injg
        simp_all[integral_image_eq_integral_abs_deriv_smul hs hg' injg]
        simp[pi_nonneg]
      }
    _= ∫ x in [[-1,1]], f x := by {
      have image : (cos '' [[0,π]]) = [[-1,1]] := by {
        ext a
        constructor
        · intro ha
          rw [@mem_image] at ha
          obtain ⟨y, hy⟩ := ha
          simp
          obtain ⟨hP, hQ⟩ := hy
          repeat rw[← hQ]
          constructor
          map_tacs [exact neg_one_le_cos y; exact cos_le_one y]
        · intro ha
          simp at ha
          obtain ⟨hP, hQ⟩ := ha
          use arccos a
          constructor
          map_tacs [exact mem_uIcc_of_le (by exact arccos_nonneg a) (by exact arccos_le_pi a); exact cos_arccos hP hQ]
      }
      simp_all
    }
    _= ∫ y in (-1)..1, f y := by {
      rw [intervalIntegral.integral_of_le]
      map_tacs [simp[integral_Icc_eq_integral_Ioc]; simp]
    }
  }
