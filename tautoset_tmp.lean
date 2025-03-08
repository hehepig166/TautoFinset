/-
Copyright (c) 2025 Lenny Taelman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lenny Taelman
-/
/-
The original tauto_set tactic is from
https://github.com/LennyTaelman/TautoSet/tree/master
I'm trying to alter it to fit Finset.
Authors: hehepig166
-/
import Mathlib

--open Finset Set
open Lean Elab.Tactic

elab (name := specialize_all) "specialize_all" x:term : tactic => withMainContext do
  for h in ← getLCtx do
    evalTactic (← `(tactic|specialize $(mkIdent h.userName) $x)) <|> pure ()

elab (name := apply_all) "apply_all" x:term : tactic => withMainContext do
  for h in ← getLCtx do
    evalTactic (← `(tactic|apply $x at $(mkIdent h.userName))) <|> pure ()


#check Set.mem_inter_iff
#check Set.diff_eq

macro "tauto_set" : tactic => `(tactic|
  · simp_all only [
      Set.ext_iff, Set.subset_def,
      Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.symmDiff_def, Set.diff_eq, Set.disjoint_iff,

      Finset.mem_univ,
      Finset.ext_iff, Finset.subset_iff,
      Finset.mem_union, Finset.mem_compl, Finset.mem_inter,
      Finset.mem_symmDiff, Finset.sdiff_eq_inter_compl, Finset.disjoint_iff_inter_eq_empty
    ]
    try intro x
    try specialize_all x
    aesop
    <;> tauto
)

--variable {α : Type} {A B C D E : Set α}
variable {α : Type*} [DecidableEq α] [Fintype α] {A B C D E : Finset α}
--variable {n : ℕ} {A B C D E : Finset (Fin n)}



example (h : B ∪ C ⊆ A ∪ A) : B ⊆ A := by tauto_set
example (h : B ∩ B ∩ C ⊇ A) : A ⊆ B := by tauto_set
example (hABC : A ⊆ B ∪ C) (hCD : C ⊆ D): A ⊆ B ∪ D := by
  --tauto_set
  simp_all only [
    Finset.ext_iff, Finset.subset_iff,
    Finset.mem_union, Finset.mem_compl, Finset.mem_inter,
    Finset.mem_symmDiff, Finset.sdiff_eq_inter_compl, Finset.disjoint_iff_inter_eq_empty
  ]
  try intro x
  try specialize_all x
  have {f : α → Prop} : (∀ ⦃x : α⦄, f x) → f x := by aesop
  try apply_all this
  <;> tauto

example (h : A = Aᶜ) : B = ∅ := by tauto_set
example (h : A = Aᶜ) : B = C := by tauto_set

example (h : A ⊆ Aᶜ \ B) : A = ∅ := by tauto_set
example (h1 : A ⊆ B \ C) : A ⊆ B := by tauto_set

example (h : Finset.univ ⊆ ((A ∪ B) ∩ C) ∩ ((Aᶜ ∩ Bᶜ) ∪ Cᶜ)) : D \ B ⊆ E ∩ Aᶜ := by
  --tauto_set
  simp_all only [
    Finset.mem_univ,
    Finset.ext_iff, Finset.subset_iff,
    Finset.mem_union, Finset.mem_compl, Finset.mem_inter,
    Finset.mem_symmDiff, Finset.sdiff_eq_inter_compl, Finset.disjoint_iff_inter_eq_empty
  ]
  try intro x
  try specialize_all x
  have {f : α → Prop} : (∀ ⦃x : α⦄, f x) → f x := by aesop
  try apply_all this
  <;> tauto


example (h : A ∩ B ⊆ C) (h2 : C ∩ D ⊆ E) : A ∩ B ∩ D ⊆ E := by tauto_set
example (h : E = Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A = E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by tauto_set
example (h : E ⊇ Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) : D ∩ (B ∪ Cᶜ) ∩ A ⊆  E ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by tauto_set

example (h1 : A = B) : A = B := by tauto_set
example (h1 : A = B) (h2 : B ⊆ C): A ⊆ C := by tauto_set

example (h1 : A ∩ B = Finset.univ) : A = Finset.univ := by tauto_set
example (h1 : A ∪ B = ∅) : A = ∅ := by tauto_set

example (h: Aᶜ ⊆ ∅) : A = Finset.univ := by tauto_set
example (h: Finset.univ ⊆ Aᶜ) : A = ∅ := by tauto_set

example : A ∩ ∅ = ∅ := by tauto_set
example : A ∪ Finset.univ = Finset.univ := by tauto_set

example : ∅ ⊆ A := by tauto_set
example : A ⊆ Finset.univ := by tauto_set

example (hAB : A ⊆ B) (hBA: B ⊆ A) : A = B := by tauto_set

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by tauto_set
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by tauto_set
example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by tauto_set

example : A ⊆ (A ∪ B) ∪ C := by tauto_set

example : A ∩ B ⊆ A := by tauto_set
example : A ⊆ A ∪ B := by tauto_set

example (hBA : B ⊆ A) (hB : Finset.univ ⊆ B): Finset.univ = A := by tauto_set

example (hAB : A ⊆ B) (hCD : C ⊆ D) : C \ B ⊆ D \ A := by tauto_set

example (hAB : Disjoint A B) (hCA : C ⊆ A) : Disjoint C (B \ D) := by tauto_set

example : Aᶜᶜᶜ = Aᶜ := by tauto_set
example : Aᶜᶜ = A := by tauto_set

example (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by tauto_set

example : (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜᶜᶜ = Cᶜ ∪ Bᶜ ∪ ∅ ∪ A ∪ ∅ := by tauto_set

example : D ∩ (B ∪ Cᶜ) ∩ A = (Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by tauto_set

example (hAB : A ⊆ B) (hBC : B ⊆ C) (hCD : C ⊆ D) (hDE : D = E) (hEA : E ⊆ A) :
    (Aᶜ ∩ B ∪ (C ∩ Bᶜ)ᶜ ∩ (Eᶜ ∪ A))ᶜ ∩ (B ∪ Eᶜᶜ)ᶜ =
    (Dᶜ ∩ C ∪ (B ∩ Aᶜ)ᶜ ∩ (Eᶜ ∪ E))ᶜ ∩ (D ∪ Cᶜᶜ)ᶜ := by tauto_set



/-
  Examples from the Matroid Decomposition Theorem Verification,
  see https://github.com/Ivan-Sergeyev/seymour, and in particular
  https://github.com/Ivan-Sergeyev/seymour/blob/d8fcfa23336efe50b09fa0939e8a4ec3a5601ae9/Seymour/ForMathlib/SetTheory.lean
-/

-- setminus_inter_union_eq_union
example : A \ (A ∩ B) ∪ B = A ∪ B := by tauto_set

-- sub_parts_eq
example (hA : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by tauto_set

-- elem_notin_set_minus_singleton
example (a : α) : a ∉ A \ {a} := by tauto_set

-- sub_union_diff_sub_union
example (hA : A ⊆ B \ C) : A ⊆ B := by tauto_set

-- singleton_inter_subset_left
example (hAB : A ∩ B = {a}) : {a} ⊆ A := by tauto_set

-- singleton_inter_subset_right
example (hAB : A ∩ B = {a}) : {a} ⊆ B := by tauto_set

-- diff_subset_parent
example (hAB : A ⊆ C) : A \ B ⊆ C := by tauto_set

-- inter_subset_parent_left
example (hAC : A ⊆ C) : A ∩ B ⊆ C := by tauto_set

-- inter_subset_parent_right
example (hBC : B ⊆ C) : A ∩ B ⊆ C := by tauto_set

-- inter_subset_union
example : A ∩ B ⊆ A ∪ B := by tauto_set

-- subset_diff_empty_eq
example (hAB : A ⊆ B) (hBA : B \ A = ∅) : A = B := by tauto_set

-- Disjoint.ni_of_in
example (hAB : Disjoint A B) (ha : a ∈ A) : a ∉ B := by tauto_set

-- disjoint_of_singleton_inter_left_wo
example (hAB : A ∩ B = {a}) : Disjoint (A \ {a}) B := by tauto_set

-- disjoint_of_singleton_inter_right_wo
example (hAB : A ∩ B = {a}) : Disjoint A (B \ {a}) := by tauto_set

-- disjoint_of_singleton_inter_both_wo
example (hAB : A ∩ B = {a}) : Disjoint (A \ {a}) (B \ {a}) := by tauto_set

-- union_subset_union_iff
example (hAC : Disjoint A C) (hBC : Disjoint B C) :
    A ∪ C ⊆ B ∪ C ↔ A ⊆ B := by
  constructor <;> (intro; try tauto_set)
  simp_all only [
    Finset.ext_iff, Finset.subset_iff,
    Finset.mem_union, Finset.mem_compl, Finset.mem_inter,
    Finset.mem_symmDiff, Finset.sdiff_eq_inter_compl, Finset.disjoint_iff_inter_eq_empty
  ]
  try intro x
  try specialize_all x
  have {f : α → Prop} : (∀ ⦃x : α⦄, f x) → f x := by aesop
  try apply_all this
  <;> tauto

-- symmDiff_eq_alt
example : symmDiff A B = (A ∪ B) \ (A ∩ B) := by tauto_set

-- symmDiff_disjoint_inter
example : Disjoint (symmDiff A B) (A ∩ B) := by tauto_set

-- symmDiff_empty_eq
example : symmDiff A ∅ = A := by tauto_set

-- empty_symmDiff_eq
example : symmDiff ∅ A = A := by tauto_set

-- symmDiff_subset_ground_right
example (hC : symmDiff A B ⊆ C) (hA : A ⊆ C) : B ⊆ C := by
  --tauto_set
  simp_all only [
    Finset.ext_iff, Finset.subset_iff,
    Finset.mem_union, Finset.mem_compl, Finset.mem_inter,
    Finset.mem_symmDiff, Finset.sdiff_eq_inter_compl, Finset.disjoint_iff_inter_eq_empty
  ]
  try intro x
  try specialize_all x
  have {f : α → Prop} : (∀ ⦃x : α⦄, f x) → f x := by aesop
  try apply_all this
  <;> tauto


-- symmDiff_subset_ground_left
example (hC : symmDiff A B ⊆ C) (hB : B ⊆ C) : A ⊆ C := by
  --tauto_set
  simp_all only [
    Finset.ext_iff, Finset.subset_iff,
    Finset.mem_union, Finset.mem_compl, Finset.mem_inter,
    Finset.mem_symmDiff, Finset.sdiff_eq_inter_compl, Finset.disjoint_iff_inter_eq_empty
  ]
  try intro x
  try specialize_all x
  have {f : α → Prop} : (∀ ⦃x : α⦄, f x) → f x := by aesop
  try apply_all this
  <;> tauto


section

open Finset Nat

example (n : ℕ) (a : Fin n → Finset ℕ)
    (A : Finset ℕ) (hA : A = Icc 1 15)
    (M : Finset ℕ) (h_subset : M ⊆ A)
    (h_disj : ∀ i j, i ≠ j → a i ∩ a j = ∅)
    (h_sub : ∀ i, a i ⊆ A)
    (h_nsub : ∀ i, ¬ a i ⊆ M) :
    #M ≤ 15 - n := by

  let B := A \ M
  let b : Fin n → Finset ℕ := fun i => a i ∩ B
  let C := Finset.univ.biUnion b

  have r1 : ∀ i, b i ≠ ∅ := by
    intro i
    specialize h_sub i
    specialize h_nsub i
    dsimp [b, B]
    tauto_set

  have r2 : ∀ i j, i ≠ j → b i ∩ b j = ∅ := by
    intro i j hij
    specialize h_disj i j hij
    dsimp [b, B]
    tauto_set

  have r3 : #(Finset.univ : Finset (Fin n)) ≤ #C := by
    apply card_le_card_biUnion
    . intro x hx y hy hxy
      exact disjoint_iff_inter_eq_empty.mpr (r2 x y hxy)
    . intro i hi
      exact nonempty_iff_ne_empty.mpr (r1 i)
  simp only [Finset.card_univ, Fintype.card_fin] at r3
  have t0 : #M ≤ #A := by
    exact card_le_card h_subset
  have t1 : #C ≤ #B := by
    exact card_le_card (by tauto_set)
  have t2 : #B = #A - #M := by
    exact card_sdiff h_subset
  have t3 : #A = 15 := by
    simp only [hA, card_Icc, reduceAdd, Nat.add_one_sub_one]
  omega

end