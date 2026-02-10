import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (((x ◇ (x ◇ y)) ◇ z) ◇ z)


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y : G, x = (((x ◇ y) ◇ (x ◇ x)) ◇ y)

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  ((x ◇ (x ◇ y)) ◇ z) = (((((x ◇ (x ◇ y)) ◇ z) ◇ x) ◇ w) ◇ w) := by
    duper [op_law]
  
  have lemma_2 (x y z : G) :
  ((x ◇ (x ◇ y)) ◇ x) = ((x ◇ z) ◇ z) := by
    duper [lemma_1, op_law]
  
  have lemma_3 (x y z : G) :
  ((x ◇ y) ◇ y) = ((x ◇ z) ◇ z) := by
    duper [lemma_2]
  
  have lemma_4 (x y z w : G) :
  (x ◇ y) = ((((x ◇ (x ◇ z)) ◇ y) ◇ w) ◇ w) := by
    duper [op_law, lemma_3]
  
  have lemma_5 (x y z : G) :
  (((x ◇ y) ◇ y) ◇ (x ◇ z)) = x := by
    duper [op_law, lemma_3]
  
  have lemma_6 (x y z w : G) :
  ((x ◇ (x ◇ y)) ◇ z) = (((((x ◇ (x ◇ y)) ◇ z) ◇ w) ◇ w) ◇ x) := by
    duper [lemma_5, op_law]
  
  have lemma_7 (x y z : G) :
  ((x ◇ (x ◇ y)) ◇ z) = ((x ◇ z) ◇ x) := by
    duper [lemma_6, lemma_4]
  
  have lemma_8 (x y z : G) :
  (x ◇ y) = ((((x ◇ y) ◇ x) ◇ z) ◇ z) := by
    duper [lemma_4, lemma_7]
  
  have lemma_9 (x y : G) :
  (((x ◇ y) ◇ x) ◇ y) = x := by
    duper [op_law, lemma_7]
  
  have lemma_10 (x y : G) :
  (((x ◇ x) ◇ y) ◇ y) = x := by
    duper [lemma_9, lemma_3]
  
  have lemma_11 (x y z : G) :
  ((((x ◇ x) ◇ y) ◇ z) ◇ z) = (x ◇ y) := by
    duper [lemma_10, lemma_3]
  
  have lemma_12 (x y : G) :
  ((x ◇ x) ◇ y) = ((x ◇ y) ◇ (x ◇ x)) := by
    duper [lemma_8, lemma_11]
  
  show _ by
    intros x y
    calc
      x = (((x ◇ x) ◇ y) ◇ y) := by
        duper [lemma_10]
      (((x ◇ x) ◇ y) ◇ y) = (((x ◇ y) ◇ (x ◇ x)) ◇ y) := by
        duper [lemma_12]
  
