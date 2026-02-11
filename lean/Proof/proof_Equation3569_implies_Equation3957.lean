import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ y) = (y ◇ ((z ◇ y) ◇ x))


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z : G, (x ◇ y) = ((y ◇ (x ◇ z)) ◇ x)

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  (((x ◇ (y ◇ z)) ◇ w) ◇ z) = (z ◇ (w ◇ (y ◇ z))) := by
    duper [op_law]
  
  have lemma_2 (x y z : G) :
  (x ◇ y) = (y ◇ (x ◇ (y ◇ (z ◇ x)))) := by
    duper [op_law, lemma_1]
  
  have lemma_3 (x y : G) :
  (x ◇ y) = (y ◇ (x ◇ (x ◇ y))) := by
    duper [lemma_2, op_law]
  
  have lemma_4 (x y : G) :
  (x ◇ y) = (y ◇ (y ◇ x)) := by
    duper [lemma_2, lemma_3]
  
  have lemma_5 (x y z : G) :
  (x ◇ (y ◇ x)) = (((z ◇ x) ◇ y) ◇ x) := by
    duper [lemma_4, op_law]
  
  have lemma_6 (x y z : G) :
  (x ◇ (y ◇ (z ◇ x))) = (((z ◇ x) ◇ y) ◇ x) := by
    duper [op_law, lemma_4]
  
  have lemma_7 (x y z : G) :
  (x ◇ (y ◇ (z ◇ x))) = (x ◇ (y ◇ x)) := by
    duper [lemma_6, lemma_5]
       
  have lemma_8 (x y : G) :
  (x ◇ (y ◇ x)) = (y ◇ x) := by
    calc
      (x ◇ (y ◇ x)) = (x ◇ (y ◇ (y ◇ x))) := by
        duper [lemma_7]
      (x ◇ (y ◇ (y ◇ x))) = (y ◇ x) := by
        duper [lemma_3]
       
  have lemma_9 (x y z : G) :
  (x ◇ y) = (z ◇ y) := by
    calc
      (x ◇ y) = (y ◇ (x ◇ y)) := by
        duper [lemma_8]
      (y ◇ (x ◇ y)) = (y ◇ (y ◇ (x ◇ y))) := by
        duper [lemma_8]
      (y ◇ (y ◇ (x ◇ y))) = (y ◇ (y ◇ y)) := by
        duper [lemma_7]
      (y ◇ (y ◇ y)) = (y ◇ (y ◇ (z ◇ y))) := by
        duper [lemma_7]
      (y ◇ (y ◇ (z ◇ y))) = (y ◇ (z ◇ y)) := by
        duper [lemma_8]
      (y ◇ (z ◇ y)) = (z ◇ y) := by
        duper [lemma_8]
       
  have lemma_10 (x y z : G) :
  (x ◇ (y ◇ z)) = (y ◇ z) := by
    calc
      (x ◇ (y ◇ z)) = ((y ◇ z) ◇ (x ◇ (y ◇ z))) := by
        duper [lemma_8]
      ((y ◇ z) ◇ (x ◇ (y ◇ z))) = ((y ◇ z) ◇ (z ◇ (y ◇ z))) := by
        duper [lemma_9]
      ((y ◇ z) ◇ (z ◇ (y ◇ z))) = (z ◇ (y ◇ z)) := by
        duper [lemma_8]
      (z ◇ (y ◇ z)) = (y ◇ z) := by
        duper [lemma_8]
       
  have lemma_11 (x y z : G) :
  (x ◇ y) = ((y ◇ (x ◇ z)) ◇ x) := by
    calc
      (x ◇ y) = (((y ◇ (x ◇ z)) ◇ x) ◇ y) := by
        duper [lemma_9]
      (((y ◇ (x ◇ z)) ◇ x) ◇ y) = (y ◇ (y ◇ ((y ◇ (x ◇ z)) ◇ x))) := by
        duper [lemma_4]
      (y ◇ (y ◇ ((y ◇ (x ◇ z)) ◇ x))) = (y ◇ ((y ◇ (x ◇ z)) ◇ x)) := by
        duper [lemma_10]
      (y ◇ ((y ◇ (x ◇ z)) ◇ x)) = ((y ◇ (x ◇ z)) ◇ x) := by
        duper [lemma_10]
  
  show _ by
    exact lemma_11

