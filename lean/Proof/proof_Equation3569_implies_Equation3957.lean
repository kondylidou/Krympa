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
  (x ◇ ((y ◇ z) ◇ w)) = (((y ◇ z) ◇ w) ◇ ((w ◇ z) ◇ x)) := by
    duper [op_law]
  
  have lemma_2 (x y z w : G) :
  (((x ◇ (y ◇ z)) ◇ w) ◇ z) = (z ◇ (w ◇ (y ◇ z))) := by
    duper [op_law]
  
  have lemma_3 (x y z w : G) :
  (x ◇ (y ◇ ((z ◇ w) ◇ x))) = (((x ◇ w) ◇ y) ◇ x) := by
    duper [lemma_2, op_law]
  
  have lemma_4 (x y z : G) :
  (x ◇ y) = (y ◇ (x ◇ (y ◇ (z ◇ x)))) := by
    duper [op_law, lemma_2]
  
  have lemma_5 (x y : G) :
  (x ◇ y) = (y ◇ (x ◇ (x ◇ y))) := by
    duper [lemma_4, op_law]
  
  have lemma_6 (x y : G) :
  ((x ◇ y) ◇ y) = (y ◇ (y ◇ (x ◇ y))) := by
    duper [lemma_4]
  
  have lemma_7 (x y z : G) :
  ((x ◇ (y ◇ (z ◇ x))) ◇ x) = ((z ◇ x) ◇ x) := by
    duper [lemma_4, op_law]
  
  have lemma_8 (x y : G) :
  (x ◇ y) = (y ◇ (y ◇ x)) := by
    duper [lemma_4, lemma_5]
  
  have lemma_9 (x y z : G) :
  (x ◇ (y ◇ z)) = ((y ◇ z) ◇ ((z ◇ y) ◇ x)) := by
    duper [a_26, lemma_1]
  
  have lemma_10 (x y z : G) :
  (x ◇ (y ◇ z)) = ((y ◇ z) ◇ (y ◇ x)) := by
    duper [lemma_9, a_26]
  
  have lemma_11 (x y z : G) :
  (x ◇ (y ◇ z)) = (z ◇ ((y ◇ z) ◇ x)) := by
    duper [a_26, lemma_8]
  
  have lemma_12 (x y z : G) :
  (x ◇ (y ◇ z)) = ((y ◇ z) ◇ (z ◇ x)) := by
    duper [a_26, lemma_8]
  
  have lemma_13 (x y z : G) :
  (x ◇ (y ◇ z)) = (z ◇ (z ◇ x)) := by
    duper [lemma_11, a_26]
  
  have lemma_14 (x y z : G) :
  (x ◇ (y ◇ z)) = (x ◇ z) := by
    duper [lemma_13, lemma_8]
  
  have lemma_15 (x y z : G) :
  (x ◇ y) = ((z ◇ y) ◇ (z ◇ x)) := by
    duper [lemma_10, lemma_14]
  
  have lemma_16 (x y z : G) :
  (x ◇ y) = ((z ◇ y) ◇ (y ◇ x)) := by
    duper [lemma_12, lemma_14]
  
  have lemma_17 (x y z : G) :
  (x ◇ (y ◇ z)) = ((z ◇ y) ◇ (y ◇ x)) := by
    duper [lemma_15, lemma_8]
  
  have lemma_18 (x y z : G) :
  (x ◇ y) = (x ◇ (y ◇ z)) := by
    duper [lemma_17, lemma_16]
  
  have lemma_19 (x y z : G) :
  (x ◇ y) = (x ◇ z) := by
    duper [lemma_18, lemma_14]
  
  show _ by
    intros x y z
    calc
      (x ◇ y) = (x ◇ (x ◇ (y ◇ (x ◇ z)))) := by
        duper [lemma_19]
      (x ◇ (x ◇ (y ◇ (x ◇ z)))) = ((y ◇ (x ◇ z)) ◇ (x ◇ x)) := by
        duper [lemma_13]
      ((y ◇ (x ◇ z)) ◇ (x ◇ x)) = ((y ◇ (x ◇ z)) ◇ x) := by
        duper [lemma_19]
  
