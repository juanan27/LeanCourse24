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
  specialize h 0
  use 0

  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro h1
  obtain ⟨x0, hx0⟩ := h1
  specialize h x0
  have h3 : q x0 := by exact h hx0
  use x0
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
     constructor
     intro h1
     intro x h
     have h3 : ∃ x, p x := by use x
     exact h1 h3
     intro hyp
     intro hyp'
     obtain ⟨x₀, hx₀⟩ := hyp'
     specialize hyp x₀
     exact hyp hx₀
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  tauto
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  by_contra pr
  apply pr
  constructor
  · intro h
    intro h2
    obtain ⟨x₀, hx₀⟩ := h
    specialize h2 x₀
    contradiction
  · intro h1
    by_contra pro
    apply pr
    constructor
    intro h
    exfalso
    contradiction
    exfalso


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
    obtain ⟨x_0, hx_0⟩  := h
    obtain hP|hQ := hx_0
    · left
      use x_0
    · right
      use x_0
  · intro h2
    obtain hP|hQ := h2
    obtain ⟨x_1, hx_1⟩  := hP
    use x_1
    left
    exact hx_1
    obtain ⟨x_2, hx_2⟩  := hQ
    use x_2
    right
    exact hx_2
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
  constructor
  unfold SurjectiveFunction at *
  intro h1
  simp at *
  intro z
  specialize h1 z
  obtain ⟨x₁, hx₁⟩ := h1
  use f x₁
  unfold SurjectiveFunction at *
  intro h2
  simp at *
  intro y
  specialize h2 y
  obtain ⟨x₂, hx₂⟩ := h2
  specialize hf x₂
  obtain ⟨x₃, hx₃⟩ := hf
  rw[← hx₃] at hx₂
  use x₃
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
    intro y
    simp
    unfold SurjectiveFunction at hf
    specialize hf ((y-1) / 2)
    obtain ⟨x₀, hx₀⟩:= hf
    use ((x₀ -12)/3)
    ring
    linarith
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  intro h
  unfold Surjective at h
  let R := {x | x ∉ f x}
  specialize h R
  obtain ⟨V, hV⟩ := h
  by_cases h1 : V ∈ f V
  -- First case: V ∈ f V
  rw[hV]at h1
  have h2 : V ∉ f V := by trivial -- or using rw[memsetOf]
  rw[← hV]at h1
  contradiction
  -- Second case: V ∉ f V
  have h3 : V ∈ R := by trivial
  rw[← hV] at h3
  contradiction
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {

  unfold SequentialLimit at *
  simp at *
  intro ε hε
  specialize hs (ε /2)
  have h1 : 0 < ε / 2 := by exact half_pos hε
  have h2 : ∃ N, ∀ (n : ℕ), N ≤ n → |s n - a| < ε / 2 := by exact hs h1
  obtain ⟨n₀, hn₀⟩ := h2
  specialize ht (ε /2)
  have h3 : ∃ N, ∀ (n : ℕ), N ≤ n → |t n - b| < ε / 2 := by exact ht h1
  obtain ⟨n₁, hn₁⟩ := h3
  use max n₀ n₁
  intro n hn
  specialize hn₀ n
  specialize hn₁ n
  have hyp0 : n₀ ≤ n := by exact le_of_max_le_left hn
  have hyp1 : n₁ ≤ n := by exact le_of_max_le_right hn
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring
_≤ |s n - a| + |t n - b|:= by exact abs_add_le (s n - a) (t n - b)
_< ε / 2 + |t n - b| := by exact (add_lt_add_iff_right |t n - b|).mpr (hn₀ hyp0)
_< ε / 2 + ε / 2 := by exact (Real.add_lt_add_iff_left (ε / 2)).mpr (hn₁ hyp1)
_= ε := by norm_num

  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  unfold SequentialLimit at *
  simp at *
  by_cases h : c = 0
  -- Trivial case : when c is 0
  intro ε hε
  use 1
  intro n hn
  rw[h]
  norm_num
  exact hε
  -- The other case: when c is not 0
  intro ε hε
  specialize hs (ε / |c|)
  have hyp : 0 < ε / |c| := by refine div_pos hε ?hb; exact abs_pos.mpr h
  have hyp' : ∃ N, ∀ (n : ℕ), N ≤ n → |s n - a| < ε / |c| := by exact hs hyp
  obtain ⟨N, hN⟩ := hyp'
  use N
  intro n hn
  specialize hN n
  have h2 : |s n - a| < ε / |c| := by exact hN hn
  have h5 := calc
    |c * s n - c * a| = |c* (s n - a)| := by ring
    _= |c| * |(s n - a)| := by exact abs_mul c (s n - a)
  rw[h5]
  have h6 : 1 / |c| > 0 := by refine one_div_pos.mpr ?_; exact abs_pos.mpr h
  have h7 : |c| * |s n - a| < |c| * (ε / |c|) := by {
    apply mul_lt_mul_of_pos_left (a := |c|) (b := |s n - a|) (c := (ε / |c|))
    exact h2
    exact abs_pos.mpr h
    }
  have h8 : |c| * (ε / |c|) = ε := by {
    field_simp
  }
  rw[h8] at h7
  assumption

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
  intro K
  specialize h₁ K
  specialize h₂ K
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  let N₀ := max n₁ n₂
  use N₀
  intro n
  specialize hn₁ n
  specialize hn₂ n
  intro hN₀
  ring
  have hyp1 : n₁≤ n := by exact le_of_max_le_left hN₀
  have hyp2 : n₂ ≤ n := by exact le_of_max_le_right hN₀
  have h1 : K * t₁ n ≤ s₁ n := by exact hn₁ hyp1
  have h2 : K * t₂ n ≤ s₂ n := by exact hn₂ hyp2
  linarith
  }
#leansearch "factorial."
/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  -- We consider the factorial n!
use Nat.factorial
unfold EventuallyGrowsFaster at *
simp
constructor
intro k
use k
intro n hn
nth_rewrite 2 [← Nat.mul_factorial_pred]
norm_num
have hk : k ≤ n +1 := by exact le_add_right_of_le hn
gcongr
exact zero_lt_succ n
exact fun n ↦ factorial_ne_zero n

  }

end Growth
