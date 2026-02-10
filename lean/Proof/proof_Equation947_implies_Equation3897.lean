import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (y ◇ ((z ◇ x) ◇ (y ◇ x)))


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ x) = ((y ◇ (z ◇ x)) ◇ x)

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  ((x ◇ y) ◇ (z ◇ y)) = (w ◇ (y ◇ (w ◇ ((x ◇ y) ◇ (z ◇ y))))) := by
    duper [op_law]
  
  have lemma_2 (x y z : G) :
  ((x ◇ y) ◇ (z ◇ y)) = (z ◇ (y ◇ y)) := by
    duper [lemma_1, op_law]
  
  have lemma_3 (x y : G) :
  (x ◇ (x ◇ (y ◇ y))) = y := by
    duper [op_law, lemma_2]
       
  have lemma_4 (x y z : G) :
  (x ◇ x) = ((y ◇ (z ◇ x)) ◇ x) := by
    calc
      (x ◇ x) = ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) := by
        duper [lemma_3]
      ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) =
        ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))))) := by
        duper [lemma_3]
      ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))))) =
        ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))))) := by
        duper [lemma_2]
      ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))))) =
        ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ x)))) := by
        duper [lemma_3]
      ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ x)))) =
        ((y ◇ (z ◇ x)) ◇ (z ◇ ((z ◇ x) ◇ (z ◇ x)))) := by
        duper [lemma_2]
      ((y ◇ (z ◇ x)) ◇ (z ◇ ((z ◇ x) ◇ (z ◇ x)))) = ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ (x ◇ x)))) := by
        duper [lemma_2]
      ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ (x ◇ x)))) = ((y ◇ (z ◇ x)) ◇ x) := by
        duper [lemma_3]
  
  show _ by
    exact lemma_4

