import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ y) = ((y ◇ (x ◇ z)) ◇ x)


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ y) = ((y ◇ (z ◇ x)) ◇ x)

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  (x ◇ (y ◇ ((x ◇ z) ◇ w))) = (((x ◇ z) ◇ y) ◇ x) := by
    duper [op_law]
  
  have lemma_2 (x y z w : G) :
  (((x ◇ (y ◇ z)) ◇ w) ◇ x) = (x ◇ (w ◇ (y ◇ x))) := by
    duper [lemma_1, op_law]
  
  have lemma_3 (x y z : G) :
  (x ◇ y) = ((((y ◇ z) ◇ x) ◇ y) ◇ x) := by
    duper [op_law, lemma_1]
  
  have lemma_4 (x y : G) :
  (x ◇ y) = (((x ◇ y) ◇ y) ◇ x) := by
    duper [lemma_3, op_law]
  
  have lemma_5 (x y : G) :
  (x ◇ y) = ((y ◇ x) ◇ x) := by
    duper [lemma_3, lemma_4]
  
  have lemma_6 (x y z : G) :
  (x ◇ (((x ◇ y) ◇ z) ◇ z)) = (((x ◇ y) ◇ z) ◇ x) := by
    duper [op_law, lemma_4]
  
  have lemma_7 (x y z : G) :
  (((x ◇ y) ◇ z) ◇ x) = (x ◇ (z ◇ (x ◇ y))) := by
    duper [lemma_6, lemma_5]
  
  have lemma_8 (x y z : G) :
  ((x ◇ y) ◇ x) = (x ◇ (y ◇ (x ◇ z))) := by
    duper [lemma_5, op_law]
  
  have lemma_9 (x y z : G) :
  (((x ◇ y) ◇ z) ◇ x) = ((x ◇ z) ◇ x) := by
    duper [lemma_7, lemma_8]
       
  have lemma_10 (x y : G) :
  ((x ◇ y) ◇ x) = (x ◇ y) := by
    calc
      ((x ◇ y) ◇ x) = (((x ◇ y) ◇ y) ◇ x) := by
        duper [lemma_9]
      (((x ◇ y) ◇ y) ◇ x) = ((y ◇ x) ◇ x) := by
        duper [lemma_5]
      ((y ◇ x) ◇ x) = (x ◇ y) := by
        duper [lemma_5]
       
  have lemma_11 (x y : G) :
  (x ◇ x) = (x ◇ y) := by
    calc
      (x ◇ x) = ((x ◇ x) ◇ x) := by
        duper [lemma_5]
      ((x ◇ x) ◇ x) = (((x ◇ y) ◇ x) ◇ x) := by
        duper [lemma_9]
      (((x ◇ y) ◇ x) ◇ x) = ((x ◇ y) ◇ x) := by
        duper [lemma_10]
      ((x ◇ y) ◇ x) = (x ◇ y) := by
        duper [lemma_10]
       
  have lemma_12 (x y z : G) :
  (x ◇ y) = (x ◇ z) := by
    calc
      (x ◇ y) = (x ◇ x) := by
        duper [lemma_11]
      (x ◇ x) = (x ◇ z) := by
        duper [lemma_11]
  
  show _ by
    intros x y z
    calc
      (x ◇ y) = ((y ◇ x) ◇ x) := by
        duper [lemma_5]
      ((y ◇ x) ◇ x) = ((y ◇ (y ◇ (z ◇ x))) ◇ x) := by
        duper [lemma_12]
      ((y ◇ (y ◇ (z ◇ x))) ◇ x) = ((y ◇ (y ◇ (z ◇ x))) ◇ (y ◇ (z ◇ x))) := by
        duper [lemma_12]
      ((y ◇ (y ◇ (z ◇ x))) ◇ (y ◇ (z ◇ x))) = ((y ◇ (z ◇ x)) ◇ y) := by
        duper [lemma_5]
      ((y ◇ (z ◇ x)) ◇ y) = ((y ◇ (z ◇ x)) ◇ x) := by
        duper [lemma_12]
  
