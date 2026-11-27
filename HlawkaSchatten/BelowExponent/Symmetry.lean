/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Defs
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Ring

/-! Relabeling a profile permutes the three matchings and can reverse their signs.
The scalar row inequality therefore suffices on descending profiles. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

private def negativeSign (j : Fin 3) (s : Fin 4) : Bool :=
  !(decide (s = 0 ∨ s = partner j 0))

private def unitSign (b : Bool) : ℝ :=
  if b then -1 else 1

private theorem sign_as_unitSign (j : Fin 3) (s : Fin 4) :
    sign j s = unitSign (negativeSign j s) := by
  by_cases h : s = 0 ∨ s = partner j 0 <;> simp [sign, negativeSign, unitSign, h]

private theorem unitSign_xor (a b : Bool) :
    unitSign (Bool.xor a b) = unitSign a * unitSign b := by
  cases a <;> cases b <;> simp [unitSign]

private theorem abs_unitSign (b : Bool) : |unitSign b| = 1 := by
  cases b <;> simp [unitSign]

/-- The relabeling of the three matchings and their two sign classes.
The Boolean case check ranges over the 24 permutations of `Fin 4` and the
6 permutations of `Fin 3`. -/
private theorem matching_relabel : ∀ e : Equiv.Perm (Fin 4),
    ∃ r : Equiv.Perm (Fin 3), ∀ j s,
      e (partner j s) = partner (r j) (e s) ∧
        negativeSign j s = Bool.xor (negativeSign (r j) (e 0)) (negativeSign (r j) (e s)) := by
  let _ : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
  let _ : Fintype (Equiv.Perm (Fin 3)) := fintypePerm
  decide

private def reindexRow (e : Equiv.Perm (Fin 4)) (r : Equiv.Perm (Fin 3)) (x : Row) : Row :=
  fun j => unitSign (negativeSign j (e 0)) * x (r.symm j)

private theorem rowEval_comp_perm (t : Profile) (e : Equiv.Perm (Fin 4)) (r : Equiv.Perm (Fin 3))
    (hr : ∀ j s, e (partner j s) = partner (r j) (e s) ∧
      negativeSign j s = Bool.xor (negativeSign (r j) (e 0)) (negativeSign (r j) (e s)))
    (x : Row) (s : Fin 4) :
    rowEval (t ∘ e) s x = rowEval t (e s) (reindexRow e r x) := by
  unfold rowEval
  calc
    _ = ∑ j, sign (r j) (e s) * (t (e s) + t (partner (r j) (e s))) *
        reindexRow e r x (r j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsign : sign j s = unitSign (negativeSign (r j) (e 0)) * sign (r j) (e s) := by
        rw [sign_as_unitSign j s, (hr j s).2, unitSign_xor, ← sign_as_unitSign (r j) (e s)]
      simp only [Function.comp_apply, reindexRow, Equiv.symm_apply_apply]
      rw [(hr j s).1, hsign]
      ring
    _ = _ := Equiv.sum_comp r fun j =>
      sign j (e s) * (t (e s) + t (partner j (e s))) * reindexRow e r x j

theorem IsSimplex.comp_perm {t : Profile} (ht : IsSimplex t) (e : Equiv.Perm (Fin 4)) :
    IsSimplex (t ∘ e) :=
  ⟨fun s => ht.1 (e s), (Equiv.sum_comp e t).trans ht.2⟩

theorem RowAt.comp_perm {q : ℝ} {t : Profile} (ht : RowAt q t) (e : Equiv.Perm (Fin 4)) :
    RowAt q (t ∘ e) := by
  obtain ⟨π, hπ, γ, hγ, hSum, hRows⟩ := ht
  obtain ⟨r, hr⟩ := matching_relabel e
  refine ⟨π ∘ e, hπ.comp_perm e, γ ∘ r, fun j => hγ (r j), ?_, ?_⟩
  · exact (Equiv.sum_comp r γ).le.trans hSum
  · intro x
    let y := reindexRow e r x
    have h := hRows y
    unfold WeightedRow at h ⊢
    simp only [Function.comp_apply]
    calc
      _ = ∑ s, π s * |rowEval t s y| ^ q := by
        simp only [rowEval_comp_perm t e r hr x]
        exact Equiv.sum_comp e fun s => π s * |rowEval t s y| ^ q
      _ ≤ ∑ j, γ j * |y j| ^ q := h
      _ = ∑ j, γ (r j) * |y (r j)| ^ q := (Equiv.sum_comp r fun j => γ j * |y j| ^ q).symm
      _ = _ := Finset.sum_congr rfl fun j _ => by
        simp only [y, reindexRow, Equiv.symm_apply_apply, abs_mul, abs_unitSign, one_mul]

theorem rowAt_comp_perm_iff {q : ℝ} {t : Profile} (e : Equiv.Perm (Fin 4)) :
    RowAt q (t ∘ e) ↔ RowAt q t := by
  refine ⟨fun h => ?_, fun h => h.comp_perm e⟩
  have hBack : (t ∘ e) ∘ e.symm = t := by
    funext s
    simp
  simpa only [hBack] using h.comp_perm e.symm

theorem exists_antitone_reindex (t : Profile) :
    ∃ e : Equiv.Perm (Fin 4), Antitone (t ∘ e) := by
  let dual : Fin 4 → ℝᵒᵈ := OrderDual.toDual ∘ t
  exact ⟨Tuple.sort dual, Tuple.monotone_sort dual⟩

/-- Extend a cover of the descending sector to the whole simplex. -/
theorem rowAt_of_ordered {q : ℝ}
    (hOrdered : ∀ t : Profile, IsSimplex t →
      t 1 ≤ t 0 ∧ t 2 ≤ t 1 ∧ t 3 ≤ t 2 → RowAt q t)
    {t : Profile} (ht : IsSimplex t) : RowAt q t := by
  obtain ⟨e, he⟩ := exists_antitone_reindex t
  apply (rowAt_comp_perm_iff e).mp
  exact hOrdered (t ∘ e) (ht.comp_perm e)
    ⟨he (by decide : (0 : Fin 4) ≤ 1), he (by decide : (1 : Fin 4) ≤ 2),
      he (by decide : (2 : Fin 4) ≤ 3)⟩

/-- Sorting preserves strict positivity of the last coordinate on the open simplex. -/
theorem rowAt_of_ordered_pos {q : ℝ}
    (hOrdered : ∀ t : Profile, IsSimplex t → 0 < t 3 →
      t 1 ≤ t 0 → t 2 ≤ t 1 → t 3 ≤ t 2 → RowAt q t)
    {t : Profile} (ht : IsSimplex t) (hPos : ∀ s, 0 < t s) : RowAt q t := by
  obtain ⟨e, he⟩ := exists_antitone_reindex t
  apply (rowAt_comp_perm_iff e).mp
  exact hOrdered (t ∘ e) (ht.comp_perm e) (hPos (e 3))
    (he (by decide : (0 : Fin 4) ≤ 1)) (he (by decide : (1 : Fin 4) ≤ 2))
    (he (by decide : (2 : Fin 4) ≤ 3))

end HlawkaSchatten.BelowExponent
