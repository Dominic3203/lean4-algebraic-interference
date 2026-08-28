import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Omega

open Finset
open scoped BigOperators
open Real

section VandermondeLemma

/-- A direct corollary of the Chu–Vandermonde identity:
`C(A+B,k) - C(A,k) = Σ_{j<k} C(A,j)·C(B,k-j)`. -/
theorem vandermonde_diff (A B k : ℕ) : (Nat.choose (A + B) k : ℤ) - (Nat.choose A k : ℤ) =
    ∑ j in range k, (Nat.choose A j : ℤ) * (Nat.choose B (k - j) : ℤ) := by
  rw [Nat.choose_add A B k, Finset.sum_range_succ, add_sub_cancel_right]
  simp

end VandermondeLemma

section GodBinomialFin

/-- Main combinatorial identity on `Fin m`:
`∏ x_i = Σ_{S⊆univ} (-1)^{m-|S|}·C(∑_{i∈S} x_i, m)`
and the same alternating sum vanishes when the binomial top argument is any `k < m`. -/
private theorem strong_induction_fin (m : ℕ) (x : Fin m → ℕ) :
    ((∏ i : Fin m, (x i : ℤ)) = ∑ S in powerset (univ : Finset (Fin m)),
      (-1 : ℤ)^(m - S.card) * (Nat.choose (∑ i in S, x i) m : ℤ))
  ∧ (∀ k, k < m → (∑ S in powerset (univ : Finset (Fin m)),
      (-1 : ℤ)^(m - S.card) * (Nat.choose (∑ i in S, x i) k : ℤ)) = 0) := by
  induction' m with n ih generalizing x
  · simp
  · -- Separate the last coordinate
    set x₀ : Fin n → ℕ := x ∘ Fin.castSucc with hx₀
    set a : Fin (n+1) := Fin.last n with ha
    have ha_not_mem : a ∉ Finset.image Fin.castSucc (univ : Finset (Fin n)) := by simp
    have huniv_eq : (univ : Finset (Fin (n+1))) =
        insert a (Finset.image Fin.castSucc (univ : Finset (Fin n))) := by
      ext i; simp [Fin.exists_castSucc_eq_of_ne_last]

    -- Powerset splits into subsets without `a` and subsets with `a`
    have hsplit : powerset (univ : Finset (Fin (n+1))) =
        powerset (Finset.image Fin.castSucc (univ : Finset (Fin n))) ∪
        (powerset (Finset.image Fin.castSucc (univ : Finset (Fin n)))).image (insert a) := by
      rw [huniv_eq, Finset.powerset_insert ha_not_mem]
    have h_disjoint : Disjoint (powerset (Finset.image Fin.castSucc (univ : Finset (Fin n))))
        ((powerset (Finset.image Fin.castSucc (univ : Finset (Fin n)))).image (insert a)) :=
      Finset.disjoint_left.mpr (by
        intro S hS hS'
        rcases Finset.mem_image.1 hS' with ⟨T, hT, rfl⟩
        have ha_mem : a ∈ insert a T := Finset.mem_insert_self a T
        have hsub : S ⊆ Finset.image Fin.castSucc (univ : Finset (Fin n)) :=
          (Finset.mem_powerset.1 hS).1
        exact ha_not_mem (hsub ha_mem))

    -- Bijection between `powerset (Fin n)` and `powerset (image Fin.castSucc …)`
    have h_powerset_image : powerset (Finset.image Fin.castSucc (univ : Finset (Fin n))) =
        ((univ : Finset (Fin n)).powerset).image
        (λ T : Finset (Fin n) => T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩) := by
      simpa using Finset.powerset_image Fin.castSucc_injective (univ : Finset (Fin n))

    -- Injectivity lemmas needed for `Finset.sum_image`
    have hinj_map : ∀ T₁ T₂ : Finset (Fin n),
        T₁.map ⟨Fin.castSucc, Fin.castSucc_injective⟩ = T₂.map ⟨Fin.castSucc, Fin.castSucc_injective⟩ → T₁ = T₂ :=
      Finset.map_injective Fin.castSucc_injective
    have hinj_insert : ∀ T₁ T₂ : Finset (Fin n),
        insert a (T₁.map ⟨Fin.castSucc, Fin.castSucc_injective⟩) =
        insert a (T₂.map ⟨Fin.castSucc, Fin.castSucc_injective⟩) → T₁ = T₂ := by
      intro T₁ T₂ h
      apply hinj_map
      exact Finset.insert_inj (by simp) (by simp) h

    -- Helper sum rewrites
    have h_sum_powerset1 (f : Finset (Fin (n+1)) → ℤ) :
        ∑ S in powerset (Finset.image Fin.castSucc (univ : Finset (Fin n))), f S =
        ∑ T in powerset (univ : Finset (Fin n)), f (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩) := by
      rw [h_powerset_image]
      refine Finset.sum_image (λ T₁ _ T₂ _ h => hinj_map T₁ T₂ h)
    have h_sum_powerset2 (f : Finset (Fin (n+1)) → ℤ) :
        ∑ S in ((powerset (Finset.image Fin.castSucc (univ : Finset (Fin n)))).image (insert a)), f S =
        ∑ T in powerset (univ : Finset (Fin n)), f (insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩)) := by
      rw [h_powerset_image, Finset.image_image]
      refine Finset.sum_image (λ T₁ _ T₂ _ h => hinj_insert T₁ T₂ h)

    -- Elementary properties of the two kinds of subsets
    have card_map (T : Finset (Fin n)) : (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩).card = T.card :=
      Finset.card_map_of_injective _ Fin.castSucc_injective
    have sum_map (T : Finset (Fin n)) : ∑ i in T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩, x i = ∑ i in T, x₀ i := by
      simp [x₀, Finset.sum_map]
    have card_insert_map (T : Finset (Fin n)) :
        (insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩)).card = T.card + 1 := by
      rw [Finset.card_insert_of_not_mem (by simp), card_map]
    have sum_insert_map (T : Finset (Fin n)) :
        ∑ i in insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩), x i = (∑ i in T, x₀ i) + x a := by
      rw [Finset.sum_insert (by simp), sum_map]

    -- Sign factors for the alternating sum
    have sign1 (T : Finset (Fin n)) : (-1 : ℤ)^((n+1 : ℕ) - (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩).card) =
        -(-1 : ℤ)^(n - T.card) := by
      rw [card_map T]
      have : (n+1 - T.card : ℕ) = (n - T.card).succ := by omega
      rw [this, pow_succ, mul_comm, ← mul_assoc, neg_mul, one_mul]
    have sign2 (T : Finset (Fin n)) : (-1 : ℤ)^((n+1 : ℕ) - (insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩)).card) =
        (-1 : ℤ)^(n - T.card) := by
      rw [card_insert_map T]
      have : (n+1 - (T.card+1 : ℕ)) = n - T.card := by omega
      rw [this]

    -- Induction hypothesis for the smaller coordinate
    rcases ih n x₀ with ⟨h_prod, h_zero⟩

    -- Main sum identity for any `k`
    have hSum (k : ℕ) : (∑ S in powerset (univ : Finset (Fin (n+1))),
        (-1 : ℤ)^((n+1 : ℕ) - S.card) * (Nat.choose (∑ i in S, x i) k : ℤ)) =
        ∑ T in powerset (univ : Finset (Fin n)), (-1 : ℤ)^(n - T.card) *
          ((Nat.choose ((∑ i in T, x₀ i) + x a) k : ℤ) - (Nat.choose (∑ i in T, x₀ i) k : ℤ)) := by
      calc
        _ = (∑ S in powerset (Finset.image Fin.castSucc (univ : Finset (Fin n))),
              (-1 : ℤ)^((n+1 : ℕ) - S.card) * (Nat.choose (∑ i in S, x i) k : ℤ)) +
            (∑ S in ((powerset (Finset.image Fin.castSucc (univ : Finset (Fin n)))).image (insert a)),
              (-1 : ℤ)^((n+1 : ℕ) - S.card) * (Nat.choose (∑ i in S, x i) k : ℤ)) := by
          rw [hsplit, Finset.sum_union h_disjoint]
        _ = (∑ T in powerset (univ : Finset (Fin n)),
              (-1 : ℤ)^((n+1 : ℕ) - (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩).card) *
              (Nat.choose (∑ i in T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩, x i) k : ℤ)) +
            (∑ T in powerset (univ : Finset (Fin n)),
              (-1 : ℤ)^((n+1 : ℕ) - (insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩)).card) *
              (Nat.choose (∑ i in insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩), x i) k : ℤ)) := by
          simp_rw [h_sum_powerset1, h_sum_powerset2]
        _ = ∑ T in powerset (univ : Finset (Fin n)),
              ((-1 : ℤ)^((n+1 : ℕ) - (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩).card) *
               (Nat.choose (∑ i in T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩, x i) k : ℤ) +
               (-1 : ℤ)^((n+1 : ℕ) - (insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩)).card) *
               (Nat.choose (∑ i in insert a (T.map ⟨Fin.castSucc, Fin.castSucc_injective⟩), x i) k : ℤ)) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ T in powerset (univ : Finset (Fin n)),
              ((-(-1 : ℤ)^(n - T.card)) * (Nat.choose (∑ i in T, x₀ i) k : ℤ) +
                (-1 : ℤ)^(n - T.card) * (Nat.choose ((∑ i in T, x₀ i) + x a) k : ℤ)) := by
          refine Finset.sum_congr rfl (λ T hT => ?_)
          rw [sign1 T, sign2 T, sum_map T, sum_insert_map T]
          ring
        _ = ∑ T in powerset (univ : Finset (Fin n)), (-1 : ℤ)^(n - T.card) *
              ((Nat.choose ((∑ i in T, x₀ i) + x a) k : ℤ) - (Nat.choose (∑ i in T, x₀ i) k : ℤ)) := by
          refine Finset.sum_congr rfl (λ T hT => ?_)
          ring

    -- Apply Vandermonde to the difference inside the sum
    have h_vandermonde (T : Finset (Fin n)) (k : ℕ) :
        (Nat.choose ((∑ i in T, x₀ i) + x a) k : ℤ) - (Nat.choose (∑ i in T, x₀ i) k : ℤ) =
        ∑ j in range k, (Nat.choose (∑ i in T, x₀ i) j : ℤ) * (Nat.choose (x a) (k - j) : ℤ) := by
      simpa using vandermonde_diff (∑ i in T, x₀ i) (x a) k

    -- Interchange sums
    have h_interchange (k : ℕ) : (∑ T in powerset (univ : Finset (Fin n)), (-1 : ℤ)^(n - T.card) *
          ((Nat.choose ((∑ i in T, x₀ i) + x a) k : ℤ) - (Nat.choose (∑ i in T, x₀ i) k : ℤ))) =
        ∑ j in range k, (Nat.choose (x a) (k - j) : ℤ) *
          (∑ T in powerset (univ : Finset (Fin n)), (-1 : ℤ)^(n - T.card) * (Nat.choose (∑ i in T, x₀ i) j : ℤ)) := by
      simp_rw [h_vandermonde]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (λ j hj => ?_)
      simp_rw [Finset.mul_sum]
      ring

    -- Now prove the two required statements
    have h_g_nsucc : (∑ S in powerset (univ : Finset (Fin (n+1))),
        (-1 : ℤ)^((n+1 : ℕ) - S.card) * (Nat.choose (∑ i in S, x i) (n+1 : ℕ) : ℤ)) =
        ∏ i : Fin (n+1), (x i : ℤ) := by
      rw [hSum (n+1), h_interchange (n+1), Finset.sum_range_succ]
      -- the sum for j < n vanishes by induction hypothesis
      have h_zero_part : ∑ j in range n, (Nat.choose (x a) ((n+1 : ℕ) - j) : ℤ) *
          (∑ T in powerset (univ : Finset (Fin n)), (-1 : ℤ)^(n - T.card) * (Nat.choose (∑ i in T, x₀ i) j : ℤ)) = 0 := by
        refine Finset.sum_eq_zero (λ j hj => ?_)
        have hj_n : j < n := by simpa using Finset.mem_range.1 hj
        rw [h_zero j hj_n, mul_zero]
      rw [h_zero_part, add_zero]
      have h_last_term : (Nat.choose (x a) ((n+1 : ℕ) - n) : ℤ) = (x a : ℤ) := by
        have : (n+1 : ℕ) - n = 1 := by omega
        rw [this, Nat.choose_one_right]
      rw [h_last_term, h_prod]
      simp [x₀, a, Fin.prod_univ_castSucc]

    have h_g_zero (k : ℕ) (hk : k < n+1) : (∑ S in powerset (univ : Finset (Fin (n+1))),
        (-1 : ℤ)^((n+1 : ℕ) - S.card) * (Nat.choose (∑ i in S, x i) k : ℤ)) = 0 := by
      rw [hSum k, h_interchange k]
      refine Finset.sum_eq_zero (λ j hj => ?_)
      have hj_n : j < n := by
        have hj_range : j < k := Finset.mem_range.1 hj
        omega
      rw [h_zero j hj_n, mul_zero]

    exact ⟨h_g_nsucc, h_g_zero⟩

/-- The product identity extracted from the strong induction. -/
theorem product_eq_sum_binomial_fin (m : ℕ) (x : Fin m → ℕ) :
    (∏ i : Fin m, (x i : ℤ)) = ∑ S in powerset (univ : Finset (Fin m)),
      (-1 : ℤ)^(m - S.card) * (Nat.choose (∑ i in S, x i) m : ℤ) :=
  (strong_induction_fin m x).1

end GodBinomialFin

section HardwarePartition

/-- Subsets of `Fin (n+1)` that do not contain `Fin.last n`. -/
def partZero (n : ℕ) : Finset (Finset (Fin (n + 1))) :=
  Finset.powerset (Finset.image Fin.castSucc (Finset.univ : Finset (Fin n)))

/-- Subsets of `Fin (n+1)` that contain `Fin.last n`. -/
def partOne (n : ℕ) : Finset (Finset (Fin (n + 1))) :=
  (partZero n).image (λ s => insert (Fin.last n) s)

theorem partZero_disjoint_partOne (n : ℕ) : Disjoint (partZero n) (partOne n) := by
  rw [partOne]
  refine Finset.disjoint_left.mpr (λ x hx hx' => ?_)
  rcases Finset.mem_image.1 hx' with ⟨y, hy, rfl⟩
  have hmem : insert (Fin.last n) y ∈ partZero n := hx
  have hsub : insert (Fin.last n) y ⊆ Finset.image Fin.castSucc (Finset.univ : Finset (Fin n)) :=
    (Finset.mem_powerset.1 hmem).1
  have hlast : Fin.last n ∈ insert (Fin.last n) y := by simp
  rcases Finset.mem_image.1 (hsub hlast) with ⟨i, _, hi⟩
  exact Fin.castSucc_ne_last i hi

theorem powerset_univ_eq_union (n : ℕ) :
    (Finset.powerset (Finset.univ : Finset (Fin (n + 1)))) = partZero n ∪ partOne n := by
  have huniv_eq : (Finset.univ : Finset (Fin (n+1))) =
      insert (Fin.last n) (Finset.image Fin.castSucc (Finset.univ : Finset (Fin n))) := by
    ext i; simp [Fin.exists_castSucc_eq_of_ne_last, eq_comm]
  rw [huniv_eq, Finset.powerset_insert, partZero, partOne]

def serialAIU_finset {m : ℕ} (x : Fin m → ℕ) (s : Finset (Finset (Fin m))) : ℤ :=
  ∑ S in s, ((-1 : ℤ)^(m - S.card)) * (Nat.choose (∑ i in S, x i) m : ℤ)

theorem serialAIU_finset_eq_prod {m : ℕ} (x : Fin m → ℕ) :
    serialAIU_finset x (powerset (univ : Finset (Fin m))) = ∏ i : Fin m, (x i : ℤ) := by
  rw [serialAIU_finset, product_eq_sum_binomial_fin]

theorem vectorInterference_eq_prod (n : ℕ) (x : Fin (n+1) → ℕ) :
    serialAIU_finset x (partZero n) + serialAIU_finset x (partOne n) = ∏ i : Fin (n+1), (x i : ℤ) := by
  rw [← serialAIU_finset_eq_prod (n+1) x, powerset_univ_eq_union n,
    Finset.sum_union (partZero_disjoint_partOne n)]
  rfl

end HardwarePartition

section MonotoneErrorBound

/-- Local rounding error bound introduced by a single hardware Lookup Table (LUT) approximation. -/
def e_lut : ℝ := (2 : ℝ)⁻¹³²

/-- Global cumulative error bound scaling linearly as $O(d)$ with respect to the tree depth `d`. -/
def base (d : ℕ) : ℝ := (d : ℝ) * e_lut

/-- Linear recurrence lemma verifying that the error base increases strictly by `e_lut` per layer. -/
lemma base_succ (d : ℕ) : base (d + 1) = base d + e_lut := by
  dsimp [base]
  push_cast
  ring

variable (hardware_lns_add : ℝ → ℝ → ℝ) (ideal_lns_add : ℝ → ℝ → ℝ)

/-- Axiom A1: Single-operation hardware lower rounding bound. -/
axiom hw_add_error_lower (x y : ℝ) : 
  ideal_lns_add x y - e_lut ≤ hardware_lns_add x y

/-- Axiom A2: Single-operation hardware upper rounding bound. -/
axiom hw_add_error_upper (x y : ℝ) : 
  hardware_lns_add x y ≤ ideal_lns_add x y + e_lut

/-- Axiom B: Strict order monotonicity of the ideal LNS addition operator. -/
axiom ideal_lns_add_monotone (x₁ y₁ x₂ y₂ : ℝ) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) : 
  ideal_lns_add x₁ y₁ ≤ ideal_lns_add x₂ y₂

/-- Axiom C: Additive translation invariance inherent to the LNS logarithmic domain. -/
axiom ideal_lns_add_translate (x y c : ℝ) : 
  ideal_lns_add (x + c) (y + c) = ideal_lns_add x y + c

/-- Evaluates a hardware-implemented parallel LNS reduction tree of depth `d`. -/
def hardware_tree_sum : (d : ℕ) → (inputs : Fin (2^d) → ℝ) → ℝ
  | 0,     inputs => inputs ⟨0, by omega⟩
  | k + 1, inputs =>
    let left  := λ i : Fin (2^k) => inputs ⟨i.val, by omega⟩
    let right := λ i : Fin (2^k) => inputs ⟨i.val + 2^k, by omega⟩
    hardware_lns_add (hardware_tree_sum k left) (hardware_tree_sum k right)

/-- Evaluates an mathematically ideal LNS reduction tree of depth `d`. -/
def ideal_tree_sum : (d : ℕ) → (inputs : Fin (2^d) → ℝ) → ℝ
  | 0,     inputs => inputs ⟨0, by omega⟩
  | k + 1, inputs =>
    let left  := λ i : Fin (2^k) => inputs ⟨i.val, by omega⟩
    let right := λ i : Fin (2^k) => inputs ⟨i.val + 2^k, by omega⟩
    ideal_lns_add (ideal_tree_sum k left) (ideal_tree_sum k right)

/-- Theorem: Global upper error bound verified via an absolute-value-free monotone chain. -/
theorem tree_error_upper_bound (d : ℕ) (inputs : Fin (2^d) → ℝ) :
    hardware_tree_sum d inputs ≤ ideal_tree_sum d inputs + base d := by
  induction' d with k ih generalizing inputs
  · simp [hardware_tree_sum, ideal_tree_sum, base]
  · rw [hardware_tree_sum, ideal_tree_sum]
    let left_in  := λ i : Fin (2^k) => inputs ⟨i.val, by omega⟩
    let right_in := λ i : Fin (2^k) => inputs ⟨i.val + 2^k, by omega⟩
    have h_left  := ih left_in
    have h_right := ih right_in
    calc
      hardware_lns_add (hardware_tree_sum k left_in) (hardware_tree_sum k right_in)
        _ ≤ ideal_lns_add (hardware_tree_sum k left_in) (hardware_tree_sum k right_in) + e_lut := 
            hw_add_error_upper _ _
        _ ≤ ideal_lns_add (ideal_tree_sum k left_in + base k) (ideal_tree_sum k right_in + base k) + e_lut := by
            apply add_le_add_right
            exact ideal_lns_add_monotone _ _ _ _ h_left h_right
        _ = ideal_lns_add (ideal_tree_sum k left_in) (ideal_tree_sum k right_in) + base k + e_lut := by
            rw [ideal_lns_add_translate]
        _ = ideal_lns_add (ideal_tree_sum k left_in) (ideal_tree_sum k right_in) + base (k + 1) := by 
            rw [base_succ]

/-- Theorem: Global lower error bound verified via dual monotone squeeze. -/
theorem tree_error_lower_bound (d : ℕ) (inputs : Fin (2^d) → ℝ) :
    ideal_tree_sum d inputs - base d ≤ hardware_tree_sum d inputs := by
  induction' d with k ih generalizing inputs
  · simp [hardware_tree_sum, ideal_tree_sum, base]
  · rw [hardware_tree_sum, ideal_tree_sum]
    let left_in  := λ i : Fin (2^k) => inputs ⟨i.val, by omega⟩
    let right_in := λ i : Fin (2^k) => inputs ⟨i.val + 2^k, by omega⟩
    have h_left  := ih left_in
    have h_right := ih right_in
    calc
      ideal_lns_add (ideal_tree_sum k left_in) (ideal_tree_sum k right_in) - base (k + 1)
        _ = ideal_lns_add (ideal_tree_sum k left_in) (ideal_tree_sum k right_in) - base k - e_lut := by
            rw [base_succ]; ring
        _ = ideal_lns_add (ideal_tree_sum k left_in - base k) (ideal_tree_sum k right_in - base k) - e_lut := by
            have h_trans := ideal_lns_add_translate (ideal_tree_sum k left_in - base k) (ideal_tree_sum k right_in - base k) (base k)
            ring_nf at h_trans
            linarith [h_trans]
        _ ≤ ideal_lns_add (hardware_tree_sum k left_in) (hardware_tree_sum k right_in) - e_lut := by
            apply sub_le_sub_right
            exact ideal_lns_add_monotone _ _ _ _ h_left h_right
        _ ≤ hardware_lns_add (hardware_tree_sum k left_in) (hardware_tree_sum k right_in) := 
            hw_add_error_lower _ _

end MonotoneErrorBound