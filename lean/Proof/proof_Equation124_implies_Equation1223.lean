import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y : G, x = (y ◇ ((y ◇ x) ◇ x))


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x : G, x = (x ◇ (((x ◇ x) ◇ x) ◇ x))

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y : G) :
  ((x ◇ y) ◇ y) = (x ◇ (y ◇ ((x ◇ y) ◇ y))) := by
    duper [op_law]
  
  have lemma_2 (x : G) :
  (x ◇ x) = ((x ◇ x) ◇ x) := by
    duper [lemma_1, op_law]
       
  have lemma_3 (x : G) :
  x = (x ◇ (((x ◇ x) ◇ x) ◇ x)) := by
    calc
      x = (x ◇ ((x ◇ x) ◇ x)) := by
        duper [op_law]
      (x ◇ ((x ◇ x) ◇ x)) = (x ◇ (((x ◇ x) ◇ x) ◇ x)) := by
        duper [lemma_2]
  
  show _ by
    exact lemma_3

