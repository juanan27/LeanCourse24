import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  sorry
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  sorry
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  sorry
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  sorry
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  sorry
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
    unfold SequentialLimit at *
    intro ε hε
    specialize hs ε
    have h1 : ∃ N, ∀ n ≥ N, |s n - a| < ε := by exact hs hε
    obtain ⟨N₀, hN₀⟩ := h1
    specialize hr N₀
    obtain ⟨N₁, hN₁⟩ := hr
    let N₂ := max N₀ N₁
    use N₂
    intro n hn
    have h2 : n ≥ N₁ := by exact le_of_max_le_right hn -- from this point, tauto already closes the goal
    --have h3 : n ≥ N₀ := by exact le_of_max_le_left hn
    --specialize hN₁ n
    --have h4 : r n ≥ N₀ := by exact hN₁ h2
    --simp
    --let k := r n
    --specialize hN₀ k
    --have hk : k ≥ N₀ := by trivial
    --have h5 : |s k - a| < ε := by exact hN₀ (hN₁ h2)
    tauto
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  unfold SequentialLimit at *
  simp at *
  intro ε hε
  specialize hs₁ ε
  specialize hs₃ ε
  have h1 : ∃ N, ∀ (n : ℕ), N ≤ n → |s₁ n - a| < ε := by exact hs₁ hε
  have h3 : ∃ N, ∀ (n : ℕ), N ≤ n → |s₃ n - a| < ε := by exact hs₃ hε
  obtain ⟨N₁, hN₁⟩ := h1
  obtain ⟨N₃, hN₃⟩ := h3
  let N₂ := max N₁ N₃
  use N₂
  intro n hn
  rw[abs_lt] -- we use the lemma given as hint
  specialize hN₁ n
  specialize hN₃ n
  have hmax1 : N₁ ≤ n := by exact le_of_max_le_left hn
  have hmax3 : N₃ ≤ n := by exact le_of_max_le_right hn
  have hyp1 : |s₁ n - a| < ε := by exact hN₁ hmax1
  rw[abs_lt] at hyp1
  have hyp3 : |s₃ n - a| < ε := by exact hN₃ hmax3
  rw[abs_lt] at hyp3
  obtain ⟨h1P, h1Q⟩ := hyp1
  obtain ⟨h3P, h3Q⟩ := hyp3
  constructor
  have h' : -ε < s₁ n - a := by exact h1P
  have h'' : s₁ n - a ≤ s₂ n - a := by exact tsub_le_tsub_right (hs₁s₂ n) a
  have h''': -ε < s₂ n - a := by exact gt_of_ge_of_gt h'' h1P
  assumption
  calc s₂ n - a ≤ s₃ n - a := by exact tsub_le_tsub_right (hs₂s₃ n) a
  _ < ε := by exact h3Q

  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext x
  constructor
  intro h
  simp at *
  obtain ⟨hP, hQ⟩ := h
  obtain ⟨x1, hx1⟩ := hP
  obtain ⟨hx1P, hx1Q⟩ := hx1
  use x1
  constructor
  constructor
  tauto
  rw[hx1Q]
  tauto
  tauto
  intro hyp
  simp at *
  obtain ⟨x₁, hx₁⟩ := hyp
  obtain ⟨hypP, hypQ⟩ := hx₁
  obtain ⟨hypP₁, hypP₂⟩ := hypP
  constructor
  use x₁
  rw[← hypQ]
  exact hypP₂
  }

/- Prove this by finding relevant lemmas in Mathlib. -/

lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext z
  constructor
  simp at *
  intro h
  by_cases h1 : z > 0
  right
  by_contra hyp
  simp at hyp
  have hyp' : z^2 < 4^2 := by {
    refine sq_lt_sq' ?h1 hyp
    linarith
  }
  linarith
  left
  simp at *
  have h' : 4^2 ≤ z^2 := by linarith
  by_contra hyp
  simp at hyp
  have hyp' : z^2 < (-4) ^ 2 := by {
  rw[sq_lt_sq]
  have hyp' : -z < 4 := by linarith
  have hb : |z| = -z := by exact abs_of_nonpos h1
  simp
  rw[hb]
  assumption
  }
  linarith
  intro h
  obtain hP|hQ := h
  by_contra h
  simp at *
  have hyp' : 4 ≤ -z := by linarith
  have h0 : z < 0 := by linarith
  have h1 : |z| = -z := by exact abs_of_neg h0
  have h2 : 4^2 ≤ (-z)^2 := by {
  rw[sq_le_sq]
  simp
  rw[h1]
  exact hyp'
  }
  have h' : (-z)^2 = z^2 := by exact neg_pow_two z
  rw[h'] at h2
  linarith
  simp at *
  have h0 : z > 0 := by linarith
  have hz : |z| = z := by exact abs_of_pos h0
  have hyp : 4^2 ≤ z^2 := by {
    refine sq_le_sq.mpr ?_
    simp
    rw[hz]
    assumption
    }
  linarith
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
open Classical

def conditionalInverse (y : β)
  (h : ∃ x : α, f x = y) : α :=
  Classical.choose h

lemma invFun_spec (y : β) (h : ∃ x, f x = y) :
    f (conditionalInverse f y h) = y :=
  Classical.choose_spec h

/- We can now define the function by cases
on whether it lies in the range of `f` or not. -/

variable [Inhabited α]
def inverse (f : α → β) (y : β) : α :=
  if h : ∃ x : α, f x = y then
    conditionalInverse f y h else default
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
use inverse f
unfold LeftInvOn
intro x hx
unfold InjOn at *
apply hf
simp [inverse]
unfold conditionalInverse


  }






/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by {
  by_contra h
  push_neg at h
  obtain ⟨x, y, hxy⟩ := h

  have hx : f x ∈ range f := by exact mem_range_self x
  have hxg : g y ∈ range g := by exact mem_range_self y
  have hxfg : f x ∈ range g := by rw[← hxy] at hxg; exact hxg
  have hxr : f x ∈ range f ∩ range g := by exact mem_inter hx hxfg
  rw[h1] at hxr
  contradiction
  }
  have h1'' : ∀ y x, g y ≠ f x := by exact fun y x a ↦ h1' x y (id (Eq.symm a))
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    intro x
    rw[h2]
    trivial
  }
  let L : Set α × Set β → Set γ := fun (x, y) ↦ (f '' x) ∪ (g '' y)
  let R : Set γ → Set α × Set β := fun x ↦ (f ⁻¹' (x), g ⁻¹' (x))

  use L, R
  constructor
  · ext X y
    unfold L R
    constructor
    · intro h
      simp at h
      simp only [id_eq]
      obtain hl|hr := h
      · obtain ⟨x₀, hx₀, hxy₀⟩ := hl
        rw[hxy₀] at hx₀
        exact hx₀
      · obtain ⟨x₀, hx₀, hxy₀⟩ := hr
        rw[hxy₀] at hx₀
        exact hx₀
    · intro h
      simp
      simp[id_eq] at h
      have h' : (∃ x, f x = y) ∨ (∃ x, g x = y) := by exact h2' y
      obtain h'l|h'r := h'
      · left
        obtain ⟨x, hx⟩ := h'l
        use x
        rw[← hx] at h
        trivial
      · right
        obtain ⟨x, hx⟩ := h'r
        use x
        rw[← hx] at h
        trivial
  · unfold R L
    ext x y
    · simp
      constructor
      intro h
      obtain hL|hR := h
      · obtain ⟨z, hz1, hz2⟩ := hL
        apply hf at hz2
        rw[hz2] at hz1
        exact hz1
      · obtain ⟨z, hz1, hz2⟩ := hR
        exfalso
        have hx : f y ∈ range f := by exact mem_range_self y
        have hxg : g z ∈ range g := by exact mem_range_self z
        have hxfg : f y ∈ range g := by rw[hz2] at hxg; exact hxg
        have hxr : f y ∈ range f ∩ range g := by exact mem_inter hx hxfg
        rw[h1] at hxr
        contradiction
      · intro h
        · left
          use y
    · simp
      constructor
      · intro h
        obtain hL|hR := h
        · obtain ⟨x₁, hx₁, h'x₁⟩ := hL
          exfalso
          have hx : f x₁ ∈ range f := by exact mem_range_self x₁
          have hxg : g y ∈ range g := by exact mem_range_self y
          have hxfg : f x₁ ∈ range g := by rw[← h'x₁] at hxg; exact hxg
          have hxr : f x₁ ∈ range f ∩ range g := by exact mem_inter hx hxfg
          rw[h1] at hxr
          contradiction
        · obtain ⟨x₁, hx₁, h'x₁⟩ := hR
          apply hg at h'x₁
          rw[← h'x₁]
          exact hx₁
      · intro h
        · right
          use y
  }
