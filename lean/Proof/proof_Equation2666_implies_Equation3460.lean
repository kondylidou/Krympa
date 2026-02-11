import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (((x ◇ y) ◇ (x ◇ z)) ◇ y)


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ x) = (x ◇ ((x ◇ y) ◇ z))

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  ((x ◇ y) ◇ (x ◇ z)) = ((x ◇ (((x ◇ y) ◇ (x ◇ z)) ◇ w)) ◇ y) := by
    duper [op_law]

  have lemma_2 (x y z : G) :
  ((x ◇ y) ◇ (x ◇ z)) = ((x ◇ x) ◇ y) := by
    duper [lemma_1, op_law]

  have lemma_3 (x y : G) :
  (((x ◇ x) ◇ y) ◇ y) = x := by
    duper [op_law, lemma_2]

  have lemma_5 (x y z : G) :
  (x ◇ x) = (x ◇ ((x ◇ y) ◇ z)) := by
    calc
      (x ◇ x) =
        ((((x ◇ x) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) := by
        duper [lemma_3]
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) =
        (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) := by
        duper [lemma_3]
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) =
        (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) := by
        rw [lemma_2]
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y)) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) =
        (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ y) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) := by
        rw [lemma_2]
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ y) ◇ y) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) =
        ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) := by
        duper [lemma_3]
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y) ◇ z)) =
        ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ z)) := by
        duper [lemma_2]
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ z)) =
        ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ z)) := by
        duper [lemma_2]
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ y) ◇ z)) =
        ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ y) ◇ z)) := by
        duper [lemma_3]
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ y) ◇ z)) = (x ◇ ((x ◇ y) ◇ z)) := by
        duper [lemma_3]

  show _ by
    exact lemma_5
