import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  sorry
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  sorry
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  sorry
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  sorry
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  sorry
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  sorry
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  sorry
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  sorry
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  sorry
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  sorry
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  sorry
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  sorry
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro h
    obtain ⟨x₀, hx₀⟩  := h
    obtain hP|hQ := hx₀
    · left
      use x₀
    · right
      use x₀
  · intro h₁
    obtain hP|hQ := h₁
    obtain ⟨x₁, hx₁⟩  := hP
    use x₁
    left
    exact hx₁
    obtain ⟨x₂, hx₂⟩  := hQ
    use x₂
    right
    exact hx₂
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  unfold SurjectiveFunction at *
  constructor
  simp at *
  · intro h
    intro y
    specialize hf y
    specialize h y
    obtain ⟨w, h₁⟩ := hf
    obtain ⟨w₁, h⟩ := h
    subst h₁
    use f w₁
    -- subst Exists.intro works as well followed by an exact h1!

  simp at *
  · intro h
    intro y
    specialize h y
    obtain ⟨x₁, hx₁⟩ := h
    specialize hf x₁
    obtain ⟨x₂, hx₂⟩ := hf
    use x₂
    rw [hx₂]
    exact hx₁

  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  unfold SurjectiveFunction at *
  intro y
  specialize hf ((y-1) / 2)
  obtain ⟨xf, hxf⟩ := hf
  simp
  use ((xf - 12) / 3)
  ring
  linarith
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  unfold Surjective at *
  intro h
  let R := {x | x ∉ f x}
  specialize h R
  obtain ⟨A, hₐ⟩ := h
  by_cases Ξ : (A ∈ f A)
  rw [hₐ] at Ξ
  have h₁ : A ∉ f A := by trivial
  -- try w mem_setOf
  rw [hₐ] at h₁
  contradiction
  have h₂ : A ∈ R := by trivial
  rw [hₐ] at Ξ
  contradiction
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
    unfold SequentialLimit at *
    intro ε hε
    have hε1 := half_pos hε
    obtain ⟨N, hN⟩ := hs (ε / 2) hε1
    obtain ⟨N', hN'⟩ := ht (ε / 2) hε1
    let N₀ := max N N'
    use N₀
    intro n hn
    simp
    have hsn : |s n - a| < ε / 2 := hN n (le_of_max_le_left hn)
    have htn : |t n - b| < ε / 2 := hN' n (le_of_max_le_right hn)
    have := calc
      |(s n + t n) - (a + b)| = |(s n - a) + (t n - b)| := by ring
      _ ≤ |s n - a| + |t n - b| := by exact abs_add (s n - a) (t n - b)
      _ < (ε / 2) + (ε / 2) := by exact add_lt_add hsn htn
      _ = ε := by ring
    exact this
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  unfold SequentialLimit at *
  simp at *
  intro ε hε
  by_cases hc : c = 0
  · simp [hc]
    use 0
    intro n hn
    exact hε
  · let ε' := ε / |c|
    have ε'pos : ε' > 0 := by exact div_pos hε (abs_pos.mpr hc)
    obtain ⟨N, hN⟩ := hs ε' ε'pos
    use N
    intro n hn
    have hε₁ : ε' = ε / |c| := by exact rfl
    calc
      |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
      _ < |c| * ε' := by exact mul_lt_mul_of_pos_left (hN n hn) (abs_pos.mpr hc)
      _ = ε := by rw [hε₁]; field_simp
  } 

section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  unfold EventuallyGrowsFaster
  simp
  intro k
  use k
  intro n hn
  exact Nat.mul_le_mul_right (s n) hn
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  unfold EventuallyGrowsFaster at *
  simp at *
  intro k
  specialize h₁ k
  specialize h₂ k
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  let N₀ := max n₁ n₂
  use N₀
  intro n
  specialize hn₁ n
  specialize hn₂ n
  intro hN₀
  ring
  have h1 : n₁ ≤ n := by exact le_of_max_le_left hN₀
  have hts1 : k * t₁ n ≤ s₁ n := by exact hn₁ h1
  have h2 : n₂ ≤ n := by exact le_of_max_le_right hN₀
  have hts2 : k * t₂ n ≤ s₂ n := by exact hn₂ h2
  linarith
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  use Nat.factorial
  unfold EventuallyGrowsFaster
  simp
  constructor
  intro k
  use k
  intro n hn
  nth_rewrite 2 [← Nat.mul_factorial_pred]
  norm_num
  have h : k ≤ n + 1 := by exact le_add_right_of_le hn
  gcongr
  · exact zero_lt_succ n
  · exact fun n ↦ factorial_ne_zero n
  }


end Growth
