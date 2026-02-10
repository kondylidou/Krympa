import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (((y ◇ (x ◇ z)) ◇ y) ◇ x)


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z w : G, x = ((y ◇ ((z ◇ w) ◇ z)) ◇ x)

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  ((x ◇ (y ◇ z)) ◇ x) = (((w ◇ y) ◇ w) ◇ ((x ◇ (y ◇ z)) ◇ x)) := by
    duper [op_law]
  
  have lemma_2 (x y z w v : G) :
  ((x ◇ y) ◇ x) = (((z ◇ ((w ◇ (y ◇ v)) ◇ w)) ◇ z) ◇ ((x ◇ y) ◇ x)) := by
    duper [lemma_1, op_law]
  
  have lemma_3 (x y z w v : G) :
  ((x ◇ y) ◇ x) = ((((z ◇ (y ◇ w)) ◇ z) ◇ ((v ◇ y) ◇ v)) ◇ ((x ◇ y) ◇ x)) := by
    duper [lemma_2, lemma_1]
       
  have lemma_4 (x y : G) :
  (((x ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) = ((y ◇ (x ◇ x)) ◇ y) := by
    calc
      (((x ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ y)) =
        ((((((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) := by
        duper [op_law]
      ((((((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) =
        ((((((x ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) := by
        duper [lemma_1]
      ((((((x ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) =
        ((((((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) := by
        duper [lemma_1]
      ((((((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) =
        (((((((x ◇ x) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) := by
        duper [lemma_1]
      (((((((x ◇ x) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) =
        ((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) := by
        duper [lemma_1]
      ((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇ y)) =
        ((y ◇ (x ◇ x)) ◇ y) := by
        duper [lemma_3]
       
  have lemma_5 (x : G) :
  (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) = (x ◇ (x ◇ x)) := by
    calc
      (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) =
        ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ x))) := by
        duper [lemma_4]
      ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ x))) =
        (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ x))) := by
        duper [lemma_4]
      (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ (x ◇ x))) =
        (x ◇ (x ◇ x)) := by
        duper [op_law]
       
  have lemma_6 (x : G) :
  ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) = (x ◇ (x ◇ x)) := by
    calc
      ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) =
        ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ x))) := by
        duper [lemma_5]
      ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ x))) =
        ((((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) := by
        duper [lemma_5]
      ((((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) =
        ((((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) := by
        duper [lemma_1]
      ((((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) =
        (x ◇ (x ◇ x)) := by
        duper [op_law]
       
  have lemma_7 (x y : G) :
  (x ◇ y) = ((x ◇ y) ◇ (x ◇ y)) := by
    calc
      (x ◇ y) = ((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ y)) ◇ (x ◇ y)) := by
        duper [op_law]
      ((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ (x ◇ y)) ◇ (x ◇ y)) =
        (((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ (x ◇ y)) ◇ (x ◇ y)) := by
        duper [lemma_6]
      (((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ (x ◇ y)) ◇ (x ◇ y)) =
        ((((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ (x ◇ y)) ◇ (x ◇ y)) := by
        duper [lemma_6]
      ((((((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ ((x ◇ y) ◇ ((x ◇ y) ◇ (x ◇ y)))) ◇ (x ◇ y)) ◇ (x ◇ y)) =
        ((x ◇ y) ◇ (x ◇ y)) := by
        duper [op_law]
       
  have lemma_8 (x y : G) :
  ((x ◇ y) ◇ x) = x := by
    calc
      ((x ◇ y) ◇ x) = (((x ◇ y) ◇ (x ◇ y)) ◇ x) := by
        duper [lemma_7]
      (((x ◇ y) ◇ (x ◇ y)) ◇ x) = ((((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ y)) ◇ x) := by
        duper [lemma_7]
      ((((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ y)) ◇ x) = x := by
        duper [op_law]
  
  show _ by
    intros x y z w
    calc
      x = ((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x) := by
        duper [lemma_8]
      ((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x) =
        ((((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x) ◇ (y ◇ ((z ◇ w) ◇ z))) ◇ ((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x)) := by
        duper [lemma_8]
      ((((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x) ◇ (y ◇ ((z ◇ w) ◇ z))) ◇ ((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x)) =
        ((y ◇ ((z ◇ w) ◇ z)) ◇ ((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x)) := by
        duper [op_law]
      ((y ◇ ((z ◇ w) ◇ z)) ◇ ((x ◇ ((y ◇ ((z ◇ w) ◇ z)) ◇ x)) ◇ x)) =
        ((y ◇ ((z ◇ w) ◇ z)) ◇ x) := by
        duper [lemma_8]
  
