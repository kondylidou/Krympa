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
    duper [op_law, lemma_1]

  have lemma_3 (x y : G) :
  (((x ◇ x) ◇ y) ◇ y) = x := by
    duper [op_law, lemma_2]

  have lemma_4 (x y : G) :
  (((x ◇ x) ◇ x) ◇ (x ◇ y)) = x := by
    duper [lemma_3, lemma_2]

  have lemma_5 (x y : G) :
  (x ◇ x) = (x ◇ ((x ◇ x) ◇ y)) := by
    duper [lemma_4, lemma_3]

  have lemma_6 (x y z : G) :
  (x ◇ x) = (x ◇ ((x ◇ y) ◇ z)) := by
    duper [a_6, lemma_5]

  show _ by
    exact lemma_6
