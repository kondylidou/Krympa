import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (y ◇ (y ◇ ((z ◇ x) ◇ x)))


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y : G, x = (y ◇ ((x ◇ x) ◇ (y ◇ x)))

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  (x ◇ ((y ◇ z) ◇ z)) = (w ◇ (w ◇ (z ◇ (x ◇ ((y ◇ z) ◇ z))))) := by
    duper [op_law]
  
  have lemma_2 (x y z : G) :
  (x ◇ ((y ◇ x) ◇ x)) = (z ◇ (z ◇ x)) := by
    duper [lemma_1, op_law]
  
  have lemma_3 (x y z : G) :
  (x ◇ (x ◇ y)) = (z ◇ (z ◇ y)) := by
    duper [lemma_2]
  
  have lemma_4 (x y z w : G) :
  (x ◇ ((y ◇ z) ◇ z)) = (z ◇ (w ◇ (w ◇ (x ◇ ((y ◇ z) ◇ z))))) := by
    duper [lemma_1, lemma_3]
  
  have lemma_5 (x y z w : G) :
  (x ◇ (x ◇ (y ◇ ((z ◇ w) ◇ w)))) = (y ◇ w) := by
    duper [op_law, lemma_3]
  
  have lemma_6 (x y z : G) :
  (x ◇ ((y ◇ z) ◇ z)) = (z ◇ (x ◇ z)) := by
    duper [lemma_5, lemma_4]
  
  have lemma_7 (x y z : G) :
  (x ◇ y) = (z ◇ (z ◇ (y ◇ (x ◇ y)))) := by
    duper [lemma_5, lemma_6]
  
  have lemma_8 (x y : G) :
  (x ◇ (y ◇ (x ◇ y))) = y := by
    duper [op_law, lemma_6]
  
  have lemma_9 (x y : G) :
  (x ◇ (x ◇ (y ◇ y))) = y := by
    duper [lemma_8, lemma_3]
  
  have lemma_10 (x y z : G) :
  (x ◇ (x ◇ (y ◇ (z ◇ z)))) = (y ◇ z) := by
    duper [lemma_9, lemma_3]
  
  have lemma_11 (x y : G) :
  (x ◇ (y ◇ y)) = ((y ◇ y) ◇ (x ◇ y)) := by
    duper [lemma_7, lemma_10]
  
  show _ by
    intros x y
    calc
      x = (y ◇ (y ◇ (x ◇ x))) := by
        duper [lemma_9]
      (y ◇ (y ◇ (x ◇ x))) = (y ◇ ((x ◇ x) ◇ (y ◇ x))) := by
        duper [lemma_11]
  
