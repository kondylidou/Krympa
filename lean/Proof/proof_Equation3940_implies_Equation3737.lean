import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ y) = ((x ◇ (z ◇ y)) ◇ z)


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ y) = ((x ◇ z) ◇ (y ◇ z))

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  (x ◇ y) = ((x ◇ (z ◇ w)) ◇ (z ◇ (y ◇ w))) := by
    duper [op_law]
       
  have lemma_2 (x y z w : G) :
  ((x ◇ y) ◇ z) = ((x ◇ (z ◇ y)) ◇ (w ◇ w)) := by
    calc
      ((x ◇ y) ◇ z) = (((x ◇ (z ◇ y)) ◇ z) ◇ z) := by
        duper [op_law]
      (((x ◇ (z ◇ y)) ◇ z) ◇ z) = ((((x ◇ (z ◇ y)) ◇ (x ◇ w)) ◇ (x ◇ (z ◇ w))) ◇ z) := by
        duper [lemma_1]
      ((((x ◇ (z ◇ y)) ◇ (x ◇ w)) ◇ (x ◇ (z ◇ w))) ◇ z) =
        ((((x ◇ (z ◇ y)) ◇ (x ◇ w)) ◇ (x ◇ ((z ◇ (w ◇ w)) ◇ w))) ◇ z) := by
        duper [op_law]
      ((((x ◇ (z ◇ y)) ◇ (x ◇ w)) ◇ (x ◇ ((z ◇ (w ◇ w)) ◇ w))) ◇ z) =
        (((x ◇ (z ◇ y)) ◇ (z ◇ (w ◇ w))) ◇ z) := by
        duper [lemma_1]
      (((x ◇ (z ◇ y)) ◇ (z ◇ (w ◇ w))) ◇ z) = ((x ◇ (z ◇ y)) ◇ (w ◇ w)) := by
        duper [op_law]
  
  have lemma_3 (x y z : G) :
  (x ◇ y) = ((x ◇ z) ◇ (y ◇ z)) := by
    duper [lemma_2, lemma_1]
  
  show _ by
    exact lemma_3

