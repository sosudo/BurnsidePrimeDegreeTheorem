import Mathlib
import Architect

namespace BurnsidePrimeDegreeTheorem
open Polynomial

/-- Helper: sum eval sub coeff. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma sum_eval_sub_coeff {K : Type*} [Field K] (U : Finset K) (q : K[X]) (r : ℕ)
    (hr : 0 < r) (hq : q.natDegree ≤ r)
    (hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0) :
    (∑ u ∈ U, (q.eval u - q.coeff 0)) = q.coeff r * (∑ u ∈ U, u^r) := by
  classical
  have he (u : K) : q.eval u = ∑ j ∈ Finset.range (r+1), q.coeff j * u^j :=
    Polynomial.eval_eq_sum_range' (by omega) u
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have h0 : (∑ u ∈ U, q.coeff 0 * u ^ 0) = ∑ u ∈ U, q.coeff 0 := by simp
  have hsplit : (∑ j ∈ Finset.range (r+1), ∑ u ∈ U, q.coeff j * u^j) =
      (∑ u ∈ U, q.coeff 0) + q.coeff r * (∑ u ∈ U, u^r) := by
    rw [← h0]
    rw [Finset.sum_range_succ]
    have hm : (∑ j ∈ Finset.range r, ∑ u ∈ U, q.coeff j * u^j) =
        ∑ u ∈ U, q.coeff 0 * u^0 := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      rw [Finset.sum_range_succ']
      have hzsum : (∑ j ∈ Finset.range s, ∑ u ∈ U, q.coeff (j+1) * u^(j+1)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [← Finset.mul_sum, hz (j+1) (by omega) (by simp at hj; omega), mul_zero]
      rw [hzsum, zero_add]
    rw [hm, Finset.mul_sum]
  rw [hsplit]
  ring

/-- Helper: translate sum coeff. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma translate_sum_coeff {K : Type*} [Field K] (U : Finset K) (f : K[X]) (r : ℕ)
    (hr : 0 < r) (hrm : r ≤ f.natDegree)
    (hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0) :
    (∑ u ∈ U, (f.comp (X + C u) - f)).coeff (f.natDegree-r) =
      (f.natDegree.choose (f.natDegree-r) : K) * f.leadingCoeff * (∑ u ∈ U, u^r) := by
  classical
  rw [Polynomial.finset_sum_coeff]
  have hc : (hasseDeriv (f.natDegree-r) f).coeff 0 = f.coeff (f.natDegree-r) := by
    simp [hasseDeriv_coeff]
  simp_rw [coeff_sub, ← taylor_apply, taylor_coeff, ← hc]
  have hq := natDegree_hasseDeriv_le f (f.natDegree-r)
  have hq' : (hasseDeriv (f.natDegree-r) f).natDegree ≤ r := by omega
  rw [sum_eval_sub_coeff U _ r hr hq' hz, hasseDeriv_coeff]
  have he : r + (f.natDegree-r) = f.natDegree := by omega
  rw [he, ← leadingCoeff]

/-- Helper: translate sum degree le. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma translate_sum_degree_le {K : Type*} [Field K] (U : Finset K) (f : K[X]) (r : ℕ)
    (hr : 0 < r) (hrm : r ≤ f.natDegree)
    (hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0) :
    (∑ u ∈ U, (f.comp (X + C u) - f)).natDegree ≤ f.natDegree-r := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [Polynomial.finset_sum_coeff]
  have hc : (hasseDeriv k f).coeff 0 = f.coeff k := by simp [hasseDeriv_coeff]
  simp_rw [coeff_sub, ← taylor_apply, taylor_coeff, ← hc]
  have hq := natDegree_hasseDeriv_le f k
  have hq' : (hasseDeriv k f).natDegree < r := by omega
  rw [sum_eval_sub_coeff U _ r hr (le_of_lt hq') hz, coeff_eq_zero_of_natDegree_lt hq']
  simp

/-- Helper: composition translate sum. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma composition_translate_sum {K : Type*} [Field K] (U : Finset K) (f : K[X]) (w : ℕ) :
    (∑ u ∈ U, (((X : K[X]) + C u)^w - X^w)).comp f =
      ∑ u ∈ U, ((f + C u)^w - f^w) := by
  classical
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [sub_comp, pow_comp, add_comp, X_comp, C_comp]

/-- Helper: choose cast ne zero of lt. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma choose_cast_ne_zero_of_lt {K : Type*} [Field K] (p m r : ℕ) [CharP K p]
    (hp : p.Prime) (hm : m < p) (hr : r ≤ m) : (m.choose r : K) ≠ 0 := by
  intro h
  have hd : p ∣ m.choose r := (CharP.cast_eq_zero_iff K p _).mp h
  have hf : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hr]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  exact (not_le_of_gt hm) (hp.dvd_factorial.mp hf)

/-- Helper: mul div pred lt. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma mul_div_pred_lt (p n : ℕ) (hp : 0 < p) : (p-1) / n * n < p := by
  have h := Nat.div_mul_le_self (p-1) n
  omega
/-- Helper: bound power index. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma bound_power_index (m n r : ℕ) (hn : 0 < n) (hnm : n ≤ m) (hr : 2*r ≤ m) :
    r ≤ n * (m / n) := by
  have hd := Nat.mod_lt m hn
  have he := Nat.mod_add_div m n
  have hw : 0 < m / n := Nat.div_pos hnm hn
  nlinarith

/-- Helper: degree bound forces linear. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma degree_bound_forces_linear (n w r : ℕ) (hn : 0 < n) (hr : 0 < r)
    (hrw : r ≤ w) (h : n*w-r ≤ n*(w-r)) : n = 1 := by
  have he : n * (w-r) + n*r = n*w := by rw [← Nat.mul_add, Nat.sub_add_cancel hrw]
  have hrnw : r ≤ n*w := by nlinarith
  have hh : (n*w-r)+r = n*w := Nat.sub_add_cancel hrnw
  nlinarith

set_option maxHeartbeats 1000000 in
/-- Helper: degree comparison linear. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma degree_comparison_linear {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p.Prime)
    (U : Finset K) (f : K[X]) (w r : ℕ)
    (hf : f ≠ 0) (hn : 0 < f.natDegree) (hw : w * f.natDegree < p)
    (hr : 0 < r) (hrw : r ≤ w)
    (hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0)
    (hs : (∑ u ∈ U, u^r) ≠ 0)
    (hid : (∑ u ∈ U, ((f.comp (X + C u))^w - f^w)) =
      ∑ u ∈ U, ((f+C u)^w-f^w)) : f.natDegree = 1 := by
  classical
  have hfr : r ≤ (f^w).natDegree := by rw [natDegree_pow]; exact hrw.trans (Nat.le_mul_of_pos_right w hn)
  have hc : ((f^w).natDegree.choose ((f^w).natDegree-r) : K) ≠ 0 :=
    choose_cast_ne_zero_of_lt p _ _ hp (by simpa [natDegree_pow] using hw) (Nat.sub_le _ _)
  have hcoeff : (∑ u ∈ U, ((f^w).comp (X + C u) - f^w)).coeff ((f^w).natDegree-r) ≠ 0 := by
    rw [translate_sum_coeff U (f^w) r hr hfr hz]
    exact mul_ne_zero (mul_ne_zero hc (leadingCoeff_ne_zero.mpr (pow_ne_zero _ hf))) hs
  have hlower := Polynomial.le_natDegree_of_ne_zero hcoeff
  have heq : (∑ u ∈ U, ((f^w).comp (X+C u)-f^w)) =
      (∑ u ∈ U, (((X : K[X])+C u)^w-X^w)).comp f := by
    rw [composition_translate_sum]
    simpa only [pow_comp] using hid
  rw [heq] at hlower
  let q : K[X] := ∑ u ∈ U, (((X : K[X])+C u)^w-X^w)
  have hq : q.natDegree ≤ w-r := by
    dsimp [q]
    have h := translate_sum_degree_le U ((X : K[X])^w) r hr (by simpa using hrw) hz
    simpa only [natDegree_X_pow, pow_comp, X_comp] using h
  have hu1 : (q.comp f).natDegree ≤ q.natDegree * f.natDegree := Polynomial.natDegree_comp_le
  have hu2 : q.natDegree * f.natDegree ≤ (w-r) * f.natDegree := Nat.mul_le_mul_right _ hq
  have hupper : (q.comp f).natDegree ≤ (w-r) * f.natDegree := hu1.trans hu2
  have : f.natDegree*w-r ≤ f.natDegree*(w-r) := by
    simpa only [natDegree_pow, natDegree_X_pow, Nat.mul_comm] using hlower.trans hupper
  exact degree_bound_forces_linear _ _ _ hn hr hrw this

/-- Helper: translate sum eq zero. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma translate_sum_eq_zero {K : Type*} [Field K] (U : Finset K) (f : K[X]) (r : ℕ)
    (hr : 0 < r) (hrm : f.natDegree < r)
    (hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0) :
    (∑ u ∈ U, (f.comp (X + C u) - f)) = 0 := by
  classical
  ext k
  rw [Polynomial.finset_sum_coeff, Polynomial.coeff_zero]
  have hc : (hasseDeriv k f).coeff 0 = f.coeff k := by simp [hasseDeriv_coeff]
  simp_rw [coeff_sub, ← taylor_apply, taylor_coeff, ← hc]
  have hq : (hasseDeriv k f).natDegree < r := by
    have h := natDegree_hasseDeriv_le f k
    omega
  rw [sum_eval_sub_coeff U _ r hr (le_of_lt hq) hz, coeff_eq_zero_of_natDegree_lt hq]
  simp

/-- Helper: degree comparison linear general. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma degree_comparison_linear_general {K : Type*} [Field K] (p : ℕ) [CharP K p] (hp : p.Prime)
    (U : Finset K) (f : K[X]) (w r : ℕ)
    (hf : f ≠ 0) (hn : 0 < f.natDegree) (hw : w * f.natDegree < p)
    (hr : 0 < r) (hrnw : r ≤ w * f.natDegree)
    (hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0)
    (hs : (∑ u ∈ U, u^r) ≠ 0)
    (hid : (∑ u ∈ U, ((f.comp (X + C u))^w - f^w)) =
      ∑ u ∈ U, ((f+C u)^w-f^w)) : f.natDegree = 1 := by
  classical
  by_cases hrw : r ≤ w
  · exact degree_comparison_linear p hp U f w r hf hn hw hr hrw hz hs hid
  · have hfr : r ≤ (f^w).natDegree := by simpa only [natDegree_pow] using hrnw
    have hc : ((f^w).natDegree.choose ((f^w).natDegree-r) : K) ≠ 0 :=
      choose_cast_ne_zero_of_lt p _ _ hp (by simpa [natDegree_pow] using hw) (Nat.sub_le _ _)
    have hcoeff : (∑ u ∈ U, ((f^w).comp (X + C u) - f^w)).coeff ((f^w).natDegree-r) ≠ 0 := by
      rw [translate_sum_coeff U (f^w) r hr hfr hz]
      exact mul_ne_zero (mul_ne_zero hc (leadingCoeff_ne_zero.mpr (pow_ne_zero _ hf))) hs
    have hzpoly : (∑ u ∈ U, (((X : K[X])+C u)^w-X^w)) = 0 := by
      have h := translate_sum_eq_zero U ((X : K[X])^w) r hr (by simpa using Nat.lt_of_not_ge hrw) hz
      simpa only [pow_comp, X_comp] using h
    have heq : (∑ u ∈ U, ((f^w).comp (X+C u)-f^w)) =
        (∑ u ∈ U, (((X : K[X])+C u)^w-X^w)).comp f := by
      rw [composition_translate_sum]
      simpa only [pow_comp] using hid
    rw [heq, hzpoly, zero_comp, coeff_zero] at hcoeff
    exact False.elim (hcoeff rfl)
/-- Helper: finite perm invariant. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma finite_perm_invariant {α : Type*} [Finite α] (e : Equiv.Perm α) (s : Set α)
    (h : ∀ x, x ∈ s → e x ∈ s) (x : α) : e x ∈ s ↔ x ∈ s := by
  classical
  let f : s → s := fun x => ⟨e x, h x x.property⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hab)
  have hs : Function.Surjective f := Finite.injective_iff_surjective.mp hi
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hs ⟨e x, hx⟩
    have : (y : α) = x := e.injective (congrArg Subtype.val hy)
    simpa [this] using y.property
  · exact h x

/-- Helper: difference power sum. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma difference_power_sum {K : Type*} [Field K] [Fintype K] (π : Equiv.Perm K)
    (U : Finset K) (h : ∀ i j, i - j ∈ U → π i - π j ∈ U)
    (i : K) (w : ℕ) :
    ∑ u ∈ U, (π (i + u)) ^ w = ∑ u ∈ U, (π i + u) ^ w := by
  classical
  apply Finset.sum_bij (fun u _ => π (i + u) - π i)
  · intro u hu
    apply h
    simpa using hu
  · intro u hu v hv he
    have he' : π (i + u) = π (i + v) := sub_left_injective he
    exact add_left_cancel (π.injective he')
  · intro v hv
    let f : {u // u ∈ U} → {u // u ∈ U} := fun u =>
      ⟨π (i + u) - π i, h (i + u) i (by simpa using u.property)⟩
    have hi : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply add_left_cancel (a := i)
      apply π.injective
      exact sub_left_injective (congrArg Subtype.val hab)
    obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hi) ⟨v, hv⟩
    exact ⟨u, u.property, congrArg Subtype.val hu⟩
  · intro u hu
    simp

open Polynomial
/-- Helper: difference polynomial identity. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma difference_polynomial_identity {K : Type*} [Field K] [Fintype K] (π : Equiv.Perm K)
    (U : Finset K) (h : ∀ i j, i - j ∈ U → π i - π j ∈ U)
    (f : K[X]) (hf : ∀ i, f.eval i = π i) (w : ℕ)
    (hd : (U.sum (fun u => (f.comp ((X : K[X]) + C u)) ^ w - (f + C u) ^ w) : K[X]).natDegree < Fintype.card K) :
    U.sum (fun u => (f.comp ((X : K[X]) + C u)) ^ w - (f + C u) ^ w) = 0 := by
  classical
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id) Function.injective_id ?_ hd
  intro i
  have hi := difference_power_sum π U h i w
  simpa only [Polynomial.eval_finset_sum, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, hf,
    Finset.sum_sub_distrib, sub_eq_zero] using hi

/-- Helper: difference polynomial degree. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma difference_polynomial_degree {K : Type*} [Field K] (U : Finset K) (f : K[X]) (w : ℕ) :
    (U.sum (fun u => (f.comp ((X : K[X]) + C u)) ^ w - (f + C u) ^ w)).natDegree ≤ w * f.natDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_pow_le.trans
    apply Nat.mul_le_mul_left
    have hh := Polynomial.natDegree_comp_le (p := f) (q := (X : K[X]) + C u)
    rw [Polynomial.natDegree_X_add_C, mul_one] at hh
    exact hh
  · apply Polynomial.natDegree_pow_le.trans
    apply Nat.mul_le_mul_left
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
/-- Helper: some power sum ne zero. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma some_power_sum_ne_zero {K : Type*} [Field K] (U : Finset K)
    (hne : U.Nonempty) (hz : (0 : K) ∉ U) :
    ∃ k, 1 ≤ k ∧ k ≤ U.card ∧ (∑ u ∈ U, u ^ k) ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  let e : Fin U.card ≃ {u // u ∈ U} := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
  let f : Fin U.card → K := fun i => (e i).val
  have hf : Function.Injective f := fun i j h => e.injective (Subtype.ext h)
  have hs (i : Fin U.card) : ∑ j : Fin U.card, f j * f j ^ (i : ℕ) = 0 := by
    have h := hn ((i : ℕ) + 1) (by omega) (by omega)
    have heq : (∑ j : Fin U.card, f j ^ ((i : ℕ) + 1)) = ∑ u ∈ U, u ^ ((i : ℕ) + 1) := by
      rw [← Finset.sum_coe_sort U]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [← heq] at h
    simpa [pow_succ, mul_comm] using h
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hs
  obtain ⟨u, hu⟩ := hne
  let i := e.symm ⟨u, hu⟩
  have hi : f i = 0 := congrFun hzero i
  have : u = 0 := by simpa [f, i] using hi
  exact hz (this ▸ hu)
open Polynomial

/-- Helper: muller degree one. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma muller_degree_one {K : Type*} [Field K] [Fintype K] (p : ℕ) [CharP K p]
    (hp : p.Prime) (hcard : Fintype.card K = p) (π : Equiv.Perm K)
    (U : Finset K) (hne : U.Nonempty) (hzero : (0 : K) ∉ U)
    (hsmall : 2 * U.card ≤ p - 1)
    (h : ∀ i j, i - j ∈ U → π i - π j ∈ U)
    (f : K[X]) (hf : ∀ i, f.eval i = π i)
    (hn : 0 < f.natDegree) (hdeg : f.natDegree < p) : f.natDegree = 1 := by
  classical
  have hf0 : f ≠ 0 := by intro hh; subst f; simp at hn
  obtain ⟨k, hk, hkU, hks⟩ := some_power_sum_ne_zero U hne hzero
  have hex : ∃ k, 0 < k ∧ (∑ u ∈ U, u^k) ≠ 0 := ⟨k, hk, hks⟩
  let r := Nat.find hex
  have hr : 0 < r := (Nat.find_spec hex).1
  have hs : (∑ u ∈ U, u^r) ≠ 0 := (Nat.find_spec hex).2
  have hrk : r ≤ k := Nat.find_min' hex ⟨hk, hks⟩
  have hz : ∀ j, 0 < j → j < r → (∑ u ∈ U, u^j) = 0 := by
    intro j hj hjr
    have hh := Nat.find_min hex hjr
    simpa [hj] using hh
  let w := (p - 1) / f.natDegree
  have hw : w * f.natDegree < p := mul_div_pred_lt p _ hp.pos
  have hrnw : r ≤ w * f.natDegree := by
    have hh := bound_power_index (p-1) f.natDegree r hn (by omega) (by omega)
    simpa [w, Nat.mul_comm] using hh
  have hd : (U.sum (fun u => (f.comp ((X : K[X]) + C u)) ^ w - (f + C u) ^ w) : K[X]).natDegree < Fintype.card K := by
    rw [hcard]; exact lt_of_le_of_lt (difference_polynomial_degree U f w) hw
  have hid0 := difference_polynomial_identity π U h f hf w hd
  have hid : (∑ u ∈ U, ((f.comp (X + C u))^w - f^w)) =
      ∑ u ∈ U, ((f+C u)^w-f^w) := by
    simp only [Finset.sum_sub_distrib] at hid0 ⊢
    linear_combination hid0
  exact degree_comparison_linear_general p hp U f w r hf0 hn hw hr hrnw hz hs hid

/-- Helper: small invariant difference set. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma small_invariant_difference_set {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (π : Equiv.Perm K) (U : Finset K) (hne : U.Nonempty) (hzero : (0 : K) ∉ U)
    (hproper : U ≠ Finset.univ.erase 0)
    (h : ∀ i j, i - j ∈ U → π i - π j ∈ U) :
    ∃ V : Finset K, V.Nonempty ∧ (0 : K) ∉ V ∧
      2 * V.card ≤ Fintype.card K - 1 ∧
      ∀ i j, i - j ∈ V → π i - π j ∈ V := by
  classical
  let T : Finset K := Finset.univ.erase 0
  have hUT : U ⊆ T := by
    intro x hx
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    exact hzero (he ▸ hx)
  let V := T \ U
  have hVne : V.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hTU : T ⊆ U := by
      intro x hx
      by_contra hxu
      have : x ∈ V := Finset.mem_sdiff.mpr ⟨hx,hxu⟩
      simp [he] at this
    exact hproper (Finset.Subset.antisymm hUT hTU)
  have hVzero : (0 : K) ∉ V := by simp [V,T]
  have hequiv (i j : K) : π i - π j ∈ U ↔ i - j ∈ U := by
    let e : Equiv.Perm (K × K) := Equiv.prodCongr π π
    let S : Set (K × K) := {x | x.1 - x.2 ∈ U}
    have hh := finite_perm_invariant e S (by intro x hx; exact h x.1 x.2 hx) (i,j)
    exact hh
  have hV (i j : K) (hij : i - j ∈ V) : π i - π j ∈ V := by
    have hh := Finset.mem_sdiff.mp hij
    have hneq : i ≠ j := by
      intro he; subst j; simp [T] at hh
    have hneq' : π i ≠ π j := fun hh => hneq (π.injective hh)
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [T, sub_ne_zero.mpr hneq']
    · intro hm; exact hh.2 ((hequiv i j).mp hm)
  have hcard : U.card + V.card = Fintype.card K - 1 := by
    have hh := Finset.card_sdiff_add_card_eq_card hUT
    simpa [V,T, Nat.add_comm] using hh
  by_cases hs : 2 * U.card ≤ Fintype.card K - 1
  · exact ⟨U, hne, hzero, hs, h⟩
  · exact ⟨V, hVne, hVzero, by omega, hV⟩

/-- Helper: muller affine. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma muller_affine {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [CharP K p] (hp : p.Prime) (hcard : Fintype.card K = p) (π : Equiv.Perm K)
    (U : Finset K) (hne : U.Nonempty) (hzero : (0 : K) ∉ U)
    (hproper : U ≠ Finset.univ.erase 0)
    (h : ∀ i j, i - j ∈ U → π i - π j ∈ U) :
    ∃ a b : K, a ≠ 0 ∧ ∀ x, π x = a*x+b := by
  classical
  obtain ⟨V, hVne, hVzero, hVsmall, hV⟩ := small_invariant_difference_set π U hne hzero hproper h
  let f : K[X] := Lagrange.interpolate Finset.univ id π
  have hf (i : K) : f.eval i = π i := by
    exact Lagrange.eval_interpolate_at_node π ((Set.injOn_id _)) (Finset.mem_univ i)
  have hf0 : f ≠ 0 := by
    intro he
    have h01 : π 0 = π 1 := by
      rw [← hf 0, ← hf 1, he]; simp
    exact zero_ne_one (π.injective h01)
  have hn : 0 < f.natDegree := by
    by_contra hh
    have he : f.natDegree = 0 := by omega
    have hc := eq_C_of_natDegree_eq_zero he
    have h01 : π 0 = π 1 := by
      rw [← hf 0, ← hf 1, hc]; simp
    exact zero_ne_one (π.injective h01)
  have hdeg : f.natDegree < p := by
    have hh := Lagrange.degree_interpolate_lt π (s := Finset.univ) (v := id) (Set.injOn_id _)
    have hh' : f.degree < (p : WithBot ℕ) := by simpa [f, hcard] using hh
    exact (natDegree_lt_iff_degree_lt hf0).2 hh'
  have hsmall : 2 * V.card ≤ p - 1 := by simpa [hcard] using hVsmall
  have hlinear := muller_degree_one p hp hcard π V hVne hVzero hsmall hV f hf hn hdeg
  obtain ⟨a, ha, b, hb⟩ := natDegree_eq_one.mp hlinear
  refine ⟨a,b,ha,?_⟩
  intro x
  rw [← hf x, ← hb]
  simp
open Equiv

/-- Helper: diff orbit preserved. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma diff_orbit_preserved {K : Type*} [AddCommGroup K] (H : Subgroup (Perm K))
    (ht : ∀ x : K, Equiv.addLeft x ∈ H) (a x u : K) (g : Perm K) (hg : g ∈ H)
    (hu : ∃ h ∈ H, h 0 = 0 ∧ h a = u) :
    ∃ h ∈ H, h 0 = 0 ∧ h a = g (x+u) - g x := by
  obtain ⟨h, hh, h0, ha⟩ := hu
  let z : Perm K := Equiv.addLeft (-g x) * g * Equiv.addLeft x * h
  refine ⟨z, H.mul_mem (H.mul_mem (H.mul_mem (ht _) hg) (ht _)) hh, ?_, ?_⟩
  · simp [z, Perm.mul_apply, h0]
  · simp [z, Perm.mul_apply, ha, sub_eq_add_neg, add_comm]

/-- Helper: diffOrbit. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
noncomputable def diffOrbit {K : Type*} [AddCommGroup K] [Fintype K]
    (H : Subgroup (Perm K)) (a : K) : Finset K := by
  classical
  exact Finset.univ.filter (fun u => ∃ h ∈ H, h 0 = 0 ∧ h a = u)

/-- Helper: diff orbit image. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma diff_orbit_image {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]
    (H : Subgroup (Perm K)) (ht : ∀ x : K, Equiv.addLeft x ∈ H)
    (a x : K) (g : Perm K) (hg : g ∈ H) :
    (diffOrbit H a).image (fun u => g (x+u) - g x) = diffOrbit H a := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    simp only [diffOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact diff_orbit_preserved H ht a x u g hg hu
  · have hi : Set.InjOn (fun u => g (x+u) - g x) (diffOrbit H a) := by
      intro u _ v _ huv
      apply add_left_cancel (a := x)
      apply g.injective
      have hh := congrArg (fun z => z + g x) huv
      simpa using hh
    rw [Finset.card_image_iff.mpr hi]

/-- Helper: exists proper diff orbit. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma exists_proper_diff_orbit {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]
    (H : Subgroup (Perm K)) (ht : ∀ x : K, Equiv.addLeft x ∈ H)
    (hnot : ¬ MulAction.IsMultiplyPretransitive H K 2) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ b ∉ diffOrbit H a := by
  classical
  by_contra hn
  push_neg at hn
  apply hnot
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  have hu : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hv : d-c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  have hm := hn (b-a) (d-c) hu hv
  simp only [diffOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  obtain ⟨h, hh, h0, hbd⟩ := hm
  let g : Perm K := Equiv.addLeft c * h * Equiv.addLeft (-a)
  refine ⟨⟨g, H.mul_mem (H.mul_mem (ht _) hh) (ht _)⟩, ?_, ?_⟩
  · simp [g, Perm.mul_apply, h0]
  · change g b = d
    simp only [g, Perm.mul_apply]
    change c + h (-a+b) = d
    rw [show -a+b = b-a by abel, hbd]
    abel

/-- Helper: diff orbit mem self. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma diff_orbit_mem_self {K : Type*} [AddCommGroup K] [Fintype K]
    (H : Subgroup (Perm K)) (a : K) : a ∈ diffOrbit H a := by
  classical
  simp only [diffOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨1, H.one_mem, rfl, rfl⟩

/-- Helper: zero not mem diff orbit. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma zero_not_mem_diff_orbit {K : Type*} [AddCommGroup K] [Fintype K]
    (H : Subgroup (Perm K)) (a : K) (ha : a ≠ 0) : 0 ∉ diffOrbit H a := by
  classical
  simp only [diffOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h, hh, h0, ha0⟩
  exact ha (h.injective (ha0.trans h0.symm))
open Equiv MulAction

/-- Helper: translations. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
noncomputable def translations (K : Type*) [AddCommGroup K] : Subgroup (Perm K) where
  carrier := {g | ∃ a, g = Equiv.addLeft a}
  one_mem' := ⟨0, by ext x; simp⟩
  mul_mem' := by
    rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
    refine ⟨a+b, ?_⟩
    ext x
    simp [Perm.mul_apply, add_assoc]
  inv_mem' := by
    rintro _ ⟨a,rfl⟩
    refine ⟨-a, ?_⟩
    ext x
    simp

/-- Helper: affine normal translations. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma affine_normal_translations {K : Type*} [Field K] (H : Subgroup (Perm K))
    (ht : ∀ a, Equiv.addLeft a ∈ H)
    (ha : ∀ g ∈ H, ∃ a b : K, a ≠ 0 ∧ ∀ x, g x = a*x+b) :
    (translations K).comap H.subtype |>.Normal := by
  refine ⟨?_⟩
  intro n hn g
  rcases hn with ⟨t, ht'⟩
  obtain ⟨a,b,_,hg⟩ := ha g g.property
  refine ⟨a*t, ?_⟩
  ext x
  change (g : Perm K) ((n : Perm K) ((g : Perm K)⁻¹ x)) = (a*t)+x
  change (n : Perm K) = Equiv.addLeft t at ht'
  rw [ht']
  change (g : Perm K) (t + (g : Perm K)⁻¹ x) = a*t + x
  rw [hg, mul_add]
  have h := hg ((g : Perm K)⁻¹ x)
  simp only [Perm.apply_inv_self] at h
  linear_combination -h

/-- Helper: affine translations regular. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma affine_translations_regular {K : Type*} [Field K] (H : Subgroup (Perm K))
    (ht : ∀ a, Equiv.addLeft a ∈ H)
    (ha : ∀ g ∈ H, ∃ a b : K, a ≠ 0 ∧ ∀ x, g x = a*x+b) :
    ∃ N : Subgroup H, N.Normal ∧ IsPretransitive N K ∧ ∀ x : K, stabilizer N x = ⊥ := by
  let N := (translations K).comap H.subtype
  have hn : N.Normal := affine_normal_translations H ht ha
  refine ⟨N,hn,?_,?_⟩
  · rw [isPretransitive_iff]
    intro x y
    let g : H := ⟨Equiv.addLeft (y-x), ht _⟩
    have hg : g ∈ N := ⟨y-x,rfl⟩
    refine ⟨⟨g,hg⟩, ?_⟩
    change (y-x)+x=y
    abel
  · intro x
    apply le_antisymm
    · intro g hg
      have hg' : (g : Perm K) x = x := hg
      obtain ⟨t, he⟩ := g.property
      change (g : Perm K) = Equiv.addLeft t at he
      rw [he] at hg'
      change t+x=x at hg'
      have ht0 : t = 0 := by exact add_right_cancel (show t+x = 0+x by simpa using hg')
      have he0 : (g : Perm K) = 1 := by rw [he, ht0]; ext z; simp
      have : g = 1 := by apply Subtype.ext; apply Subtype.ext; exact he0
      simpa using this
    · exact bot_le

/-- Helper: prime field result. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma prime_field_result {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p : ℕ) [CharP K p] (hp : p.Prime) (hcard : Fintype.card K = p)
    (H : Subgroup (Perm K)) (ht : ∀ x : K, Equiv.addLeft x ∈ H)
    (hnot : ¬ IsMultiplyPretransitive H K 2) :
    ∃ N : Subgroup H, N.Normal ∧ IsPretransitive N K ∧ ∀ x : K, stabilizer N x = ⊥ := by
  classical
  obtain ⟨a,b,ha,hb,hbU⟩ := exists_proper_diff_orbit H ht hnot
  let U := diffOrbit H a
  have hne : U.Nonempty := ⟨a, diff_orbit_mem_self H a⟩
  have hz : (0 : K) ∉ U := zero_not_mem_diff_orbit H a ha
  have hproper : U ≠ Finset.univ.erase 0 := by
    intro he
    apply hbU
    change b ∈ U
    rw [he]
    simp [hb]
  apply affine_translations_regular H ht
  intro g hg
  apply muller_affine p hp hcard g U hne hz hproper
  intro i j hij
  have hdiff := diff_orbit_preserved H ht a j (i-j) g hg
  have hu : ∃ h ∈ H, h 0 = 0 ∧ h a = i-j := by
    simpa [U, diffOrbit] using hij
  have hh := hdiff hu
  have : g (j + (i-j)) - g j ∈ U := by
    simpa [U, diffOrbit] using hh
  simpa using this
open Equiv MulAction

/-- Helper: permCoordinate. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
noncomputable def permCoordinate {A B : Type*} (e : A ≃ B) : Perm A ≃* Perm B where
  toEquiv := e.permCongr
  map_mul' f g := by ext x; simp [Equiv.permCongr_apply, Perm.mul_apply]

/-- Helper: transport prime result. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma transport_prime_result {A K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (e : K ≃ A) (G : Subgroup (Perm A))
    (H : Subgroup (Perm K)) (hH : H = G.map (permCoordinate e.symm).toMonoidHom)
    (hnot : ¬ IsMultiplyPretransitive G A 2)
    (hresult : ¬ IsMultiplyPretransitive H K 2 →
      ∃ N : Subgroup H, N.Normal ∧ IsPretransitive N K ∧ ∀ x : K, stabilizer N x = ⊥) :
    ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N A ∧ ∀ x : A, stabilizer N x = ⊥ := by
  classical
  let c : Perm A ≃* Perm K := permCoordinate e.symm
  let φ : G ≃* H := (c.subgroupMap G).trans (MulEquiv.subgroupCongr hH.symm)
  have hc (g : G) (x : K) : e (((φ g : H) : Perm K) x) = ((g : Perm A) (e x)) := by
    change e ((c (g : Perm A)) x) = _
    simp [c, permCoordinate, Equiv.permCongr_apply]
  have hn : ¬ IsMultiplyPretransitive H K 2 := by
    intro hh
    apply hnot
    apply is_two_pretransitive_iff.mpr
    intro a b c d hab hcd
    have h2 : ∀ {a b c d : K}, a ≠ b → c ≠ d → ∃ g : H, g • a = c ∧ g • b = d := is_two_pretransitive_iff.mp hh
    have hi := h2 (a := e.symm a) (b := e.symm b)
      (c := e.symm c) (d := e.symm d) (by simpa using hab) (by simpa using hcd)
    obtain ⟨g,hg1,hg2⟩ := hi
    change ((g : Perm K) (e.symm a)) = e.symm c at hg1
    change ((g : Perm K) (e.symm b)) = e.symm d at hg2
    refine ⟨φ.symm g, ?_, ?_⟩
    · have h := hc (φ.symm g) (e.symm a)
      simpa [hg1] using h.symm
    · have h := hc (φ.symm g) (e.symm b)
      simpa [hg2] using h.symm
  obtain ⟨N,hN,htrans,hfree⟩ := hresult hn
  let M := N.comap φ.toMonoidHom
  refine ⟨M, hN.comap _, ?_, ?_⟩
  · rw [isPretransitive_iff]
    intro x y
    letI := htrans
    obtain ⟨g,hg⟩ := exists_smul_eq N (e.symm x) (e.symm y)
    let k : G := φ.symm g
    have hk : k ∈ M := by change φ k ∈ N; simpa [k] using g.property
    refine ⟨⟨k,hk⟩, ?_⟩
    have hh := hc k (e.symm x)
    change ((g : H) : Perm K) (e.symm x) = e.symm y at hg
    simpa [k, hg] using hh.symm
  · intro x
    apply le_antisymm
    · intro g hg
      have hg' : ((g : G) : Perm A) x = x := hg
      have hfix : (⟨φ (g : G), g.property⟩ : N) • e.symm x = e.symm x := by
        apply e.injective
        have hh := hc (g : G) (e.symm x)
        simpa [hg'] using hh
      have hmem : (⟨φ (g : G), g.property⟩ : N) ∈ stabilizer N (e.symm x) := hfix
      rw [hfree, Subgroup.mem_bot] at hmem
      have hφ : φ (g : G) = 1 := congrArg Subtype.val hmem
      have hg1 : (g : G) = 1 := φ.injective (by simpa using hφ)
      have : g = 1 := Subtype.ext hg1
      simpa using this
    · exact bot_le

/-- Helper: regularOrbitEquiv. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
noncomputable def regularOrbitEquiv {H A : Type*} [Group H] [MulAction H A]
    [IsPretransitive H A] (a : A) (ha : stabilizer H a = ⊥) : H ≃ A :=
  Equiv.ofBijective (fun g => g • a) (by
    constructor
    · intro g h hgh
      change g • a = h • a at hgh
      have hh : h⁻¹ * g ∈ stabilizer H a := by
        change (h⁻¹ * g) • a = a
        rw [mul_smul, hgh, inv_smul_smul]
      rw [ha, Subgroup.mem_bot] at hh
      exact (inv_mul_eq_one.mp hh).symm
    · intro b
      exact exists_smul_eq H a b)

/-- Helper: regularOrbitEquiv smul. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma regularOrbitEquiv_smul {H A : Type*} [Group H] [MulAction H A]
    [IsPretransitive H A] (a : A) (ha : stabilizer H a = ⊥) (g h : H) :
    regularOrbitEquiv a ha (g*h) = g • regularOrbitEquiv a ha h := by
  exact mul_smul g h a

/-- Helper: zmodRegularEquiv. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
noncomputable def zmodRegularEquiv {H A : Type*} [Group H] [MulAction H A]
    [IsPretransitive H A] (a : A) (ha : stabilizer H a = ⊥) (p : ℕ)
    (e : Multiplicative (ZMod p) ≃* H) : ZMod p ≃ A :=
  (Equiv.mk Multiplicative.ofAdd Multiplicative.toAdd (fun _ => rfl) (fun _ => rfl)).trans
    (e.toEquiv.trans (regularOrbitEquiv a ha))

/-- Helper: zmodRegularEquiv add. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma zmodRegularEquiv_add {H A : Type*} [Group H] [MulAction H A]
    [IsPretransitive H A] (a : A) (ha : stabilizer H a = ⊥) (p : ℕ)
    (e : Multiplicative (ZMod p) ≃* H) (x y : ZMod p) :
    zmodRegularEquiv a ha p e (x+y) = e (Multiplicative.ofAdd x) • zmodRegularEquiv a ha p e y := by
  change e (Multiplicative.ofAdd (x+y)) • a = e (Multiplicative.ofAdd x) • (e (Multiplicative.ofAdd y) • a)
  rw [show Multiplicative.ofAdd (x+y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y by rfl, map_mul, mul_smul]

/-- Helper: coordinate contains translations. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma coordinate_contains_translations {A : Type*} [Fintype A] (G : Subgroup (Perm A))
    (P : Subgroup G) [IsPretransitive P A] (a : A) (ha : stabilizer P a = ⊥) (p : ℕ)
    (iso : Multiplicative (ZMod p) ≃* P) :
    let e := zmodRegularEquiv a ha p iso
    ∀ x : ZMod p, Equiv.addLeft x ∈ G.map (permCoordinate e.symm).toMonoidHom := by
  classical
  dsimp only
  intro x
  let e := zmodRegularEquiv a ha p iso
  let g : G := iso (Multiplicative.ofAdd x)
  refine ⟨g, g.property, ?_⟩
  ext y
  change e.symm ((g : Perm A) (e y)) = x + y
  apply e.injective
  simpa [g] using (zmodRegularEquiv_add a ha p iso x y).symm
/-- Helper: prime degree cycle. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma prime_degree_cycle {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Perm α)}
    (ht : IsPretransitive G α) (hp : (Fintype.card α).Prime) :
    ∃ σ : G, (σ : Perm α).IsCycle ∧ (σ : Perm α).support = Finset.univ := by
  classical
  letI := ht
  letI : Fact (Fintype.card α).Prime := ⟨hp⟩
  letI : Nonempty α := Fintype.card_pos_iff.mp hp.pos
  let a : α := Classical.choice inferInstance
  have hd : Fintype.card α ∣ Fintype.card G := by
    have h := (MulAction.stabilizer G a).card_quotient_dvd_card
    rw [← Subgroup.index_eq_card, index_stabilizer_of_transitive, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card] at h
    exact h
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) hd
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (Subgroup.orderOf_coe σ).trans hσ
  have hσ2 : (σ : Perm α).IsCycle := Perm.isCycle_of_prime_order'' hp hσ1
  refine ⟨σ, hσ2, ?_⟩
  exact Finset.eq_univ_of_card _ (hσ2.orderOf.symm.trans hσ1)


/-- Helper: prime sq not dvd factorial. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma prime_sq_not_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ p.factorial := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  intro h
  rw [Nat.factorial_succ, pow_two] at h
  have hd : n + 1 ∣ n.factorial := (Nat.mul_dvd_mul_iff_left (Nat.succ_pos n)).mp h
  exact (not_le_of_gt (Nat.lt_succ_self n)) (hp.dvd_factorial.mp hd)

/-- Helper: sylow card eq prime. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma sylow_card_eq_prime {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p H) (hd : p ∣ Nat.card H) (hnd : ¬ p ^ 2 ∣ Nat.card H) :
    Nat.card P = p := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hpdiv : p ∣ Nat.card P := P.dvd_card_of_dvd_card hd
  cases n with
  | zero => simp only [hn, pow_zero] at hpdiv; exact (hp.out.not_dvd_one hpdiv).elim
  | succ n =>
    cases n with
    | zero => simpa using hn
    | succ n =>
      exfalso
      apply hnd
      apply dvd_trans _ P.1.card_subgroup_dvd_card
      rw [hn]
      exact pow_dvd_pow p (by omega)

/-- Helper: prime degree sylow card. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma prime_degree_sylow_card {α : Type*} [Fintype α] {G : Subgroup (Perm α)}
    (ht : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (P : Sylow (Fintype.card α) G) : Nat.card P = Fintype.card α := by
  classical
  letI := ht
  letI : Fact (Fintype.card α).Prime := ⟨hp⟩
  letI : Nonempty α := Fintype.card_pos_iff.mp hp.pos
  let a : α := Classical.choice inferInstance
  have hd : Fintype.card α ∣ Nat.card G := by
    have h := (MulAction.stabilizer G a).card_quotient_dvd_card
    rw [← Subgroup.index_eq_card, index_stabilizer_of_transitive, Nat.card_eq_fintype_card] at h
    exact h
  have hg : Nat.card G ∣ (Fintype.card α).factorial := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using G.card_subgroup_dvd_card
  exact sylow_card_eq_prime P hd (fun h ↦ prime_sq_not_dvd_factorial hp (h.trans hg))

/-- Helper: prime degree sylow transitive. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma prime_degree_sylow_transitive {α : Type*} [Fintype α] {G : Subgroup (Perm α)}
    (ht : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (P : Sylow (Fintype.card α) G) : IsPretransitive P α := by
  classical
  letI : Fact (Fintype.card α).Prime := ⟨hp⟩
  have hc := prime_degree_sylow_card ht hp P
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := P) (Fintype.card α) (by rw [hc])
  have hg' : orderOf (g : Perm α) = Fintype.card α := by
    rw [← Subgroup.orderOf_coe (g : P), ← Subgroup.orderOf_coe (g : G)] at hg
    exact hg
  have hcyc : (g : Perm α).IsCycle := Perm.isCycle_of_prime_order'' hp hg'
  have hs : (g : Perm α).support = Finset.univ := Finset.eq_univ_of_card _ (hcyc.orderOf.symm.trans hg')
  rw [isPretransitive_iff]
  intro a b
  have ha : (g : Perm α) a ≠ a := by rw [← Perm.mem_support, hs]; exact Finset.mem_univ a
  have hb : (g : Perm α) b ≠ b := by rw [← Perm.mem_support, hs]; exact Finset.mem_univ b
  have hsame := (Perm.isCycle_iff_sameCycle ha).mp hcyc |>.mpr hb
  obtain ⟨n, hn⟩ := hsame
  exact ⟨g ^ n, hn⟩

/-- Helper: normal of stabilizer le normalizer. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma normal_of_stabilizer_le_normalizer {α : Type*} {H : Type*} [Group H] [MulAction H α]
    (P : Subgroup H) [IsPretransitive P α] (a : α)
    (h : stabilizer H a ≤ P.normalizer) : P.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  intro g hg
  obtain ⟨p, hp⟩ := exists_smul_eq P a (g • a)
  have hs : (p : H)⁻¹ * g ∈ stabilizer H a := by
    change ((p : H)⁻¹ * g) • a = a
    rw [mul_smul, ← hp]
    exact inv_smul_smul (p : H) a
  have hp' : (p : H) ∈ P.normalizer := Subgroup.le_normalizer p.property
  have hg' := P.normalizer.mul_mem hp' (h hs)
  simpa using hg'

/-- Helper: prime degree normal sylow regular. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma prime_degree_normal_sylow_regular {α : Type*} [Fintype α] {G : Subgroup (Perm α)}
    (ht : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (P : Sylow (Fintype.card α) G) (hn : (P : Subgroup G).Normal) :
    ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N α ∧ ∀ a : α, stabilizer N a = ⊥ := by
  classical
  letI : Fact (Fintype.card α).Prime := ⟨hp⟩
  letI : IsPretransitive P α := prime_degree_sylow_transitive ht hp P
  letI : IsCyclic P := isCyclic_of_prime_card (prime_degree_sylow_card ht hp P)
  letI : IsMulCommutative P := ⟨⟨fun a b => mul_comm a b⟩⟩
  refine ⟨P, hn, inferInstance, ?_⟩
  intro a
  apply le_antisymm
  · intro n hn
    have ha : n • a = a := hn
    have hf : ∀ b : α, n • b = b := by
      intro b
      obtain ⟨m, hm⟩ := exists_smul_eq P a b
      rw [← hm, ← mul_smul, mul_comm n m, mul_smul, ha]
    have he : (n : Perm α) = 1 := by
      ext b
      exact hf b
    have : n = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact he
    simpa using this
  · exact bot_le

/-- Helper: full assembly. Proof: by the polynomial, action, or group calculation displayed below. -/
@[blueprint "BurnsidePrimeDegreeTheorem.MainTheorem"]
lemma full_assembly {α : Type*} [Fintype α] {G : Subgroup (Perm α)}
    (ht : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (hnot : ¬ IsMultiplyPretransitive G α 2) :
    ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N α ∧ ∀ a : α, stabilizer N a = ⊥ := by
  classical
  let p := Fintype.card α
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nonempty α := Fintype.card_pos_iff.mp hp.pos
  let P : Sylow p G := Classical.choice inferInstance
  letI : IsPretransitive P α := prime_degree_sylow_transitive ht hp P
  have hc : Nat.card P = p := prime_degree_sylow_card ht hp P
  letI : IsCyclic P := isCyclic_of_prime_card hc
  letI : IsMulCommutative P := ⟨⟨fun a b => mul_comm a b⟩⟩
  let a : α := Classical.choice inferInstance
  have ha : stabilizer P a = ⊥ := by
    apply le_antisymm
    · intro n hn
      have hna : n • a = a := hn
      have hf : ∀ b : α, n • b = b := by
        intro b
        obtain ⟨m, hm⟩ := exists_smul_eq P a b
        rw [← hm, ← mul_smul, mul_comm n m, mul_smul, hna]
      have he : (n : Perm α) = 1 := by ext b; exact hf b
      have : n = 1 := by apply Subtype.ext; apply Subtype.ext; exact he
      simpa using this
    · exact bot_le
  let iso : Multiplicative (ZMod p) ≃* P := by
    have h := zmodCyclicMulEquiv (G := P) inferInstance
    rw [hc] at h
    exact h
  let e := zmodRegularEquiv a ha p iso
  let H : Subgroup (Perm (ZMod p)) := G.map (permCoordinate e.symm).toMonoidHom
  have hH : H = G.map (permCoordinate e.symm).toMonoidHom := rfl
  have htrans : ∀ x : ZMod p, Equiv.addLeft x ∈ H := coordinate_contains_translations G P a ha p iso
  apply transport_prime_result e G H hH hnot
  intro hHnot
  exact prime_field_result p hp (ZMod.card p) H htrans hHnot

end BurnsidePrimeDegreeTheorem
