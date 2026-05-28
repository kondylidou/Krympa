import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

set_option linter.style.longLine false

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation_a1 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (x ◇ (y ◇ ((z ◇ x) ◇ y)))


abbrev Equation_conjecture0 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = (x ◇ (y ◇ (z ◇ (x ◇ z))))

theorem Equation_a1_implies_Equation_conjecture0 (G : Type _) [Magma G]
    (op_law : Equation_a1 G) : Equation_conjecture0 G :=
  have lemma_1 (x y z w : G) :
  (x ◇ ((y ◇ z) ◇ x)) = ((x ◇ ((y ◇ z) ◇ x)) ◇ (w ◇ (z ◇ w))) := by
    duper [op_law]

  have lemma_2 (x y z w v : G) :
  (x ◇ (y ◇ x)) = ((x ◇ (y ◇ x)) ◇ (z ◇ ((w ◇ ((v ◇ y) ◇ w)) ◇ z))) := by
    duper [lemma_1, op_law]

  have lemma_3 (x y z w v u : G) :
  (x ◇ ((y ◇ ((z ◇ w) ◇ y)) ◇ x)) =
      ((x ◇ ((y ◇ ((z ◇ w) ◇ y)) ◇ x)) ◇ (v ◇ ((u ◇ (w ◇ u)) ◇ v))) := by
    duper [lemma_1]

  have lemma_4 (x y z w v : G) :
  (x ◇ (y ◇ x)) = ((x ◇ (y ◇ x)) ◇ ((z ◇ (y ◇ z)) ◇ (w ◇ ((v ◇ y) ◇ w)))) := by
    duper [lemma_2, lemma_1]

  have lemma_5 (x y z w : G) :
  (x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x)) =
      ((x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x)) ◇ (w ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ w))) := by
    duper [lemma_4, lemma_3]

  have lemma_6 (x y z w : G) :
  ((x ◇ ((y ◇ x) ◇ x)) ◇ z) =
      (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ ((w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ (z ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z)))) := by
    duper [op_law, lemma_5]

  have lemma_7 (x y z w : G) :
  ((x ◇ ((y ◇ x) ◇ x)) ◇ z) =
      (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w))) := by
    duper [lemma_6, lemma_5]

  have lemma_8 (x y z w : G) :
  (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) =
      ((x ◇ ((y ◇ x) ◇ x)) ◇ z) := by
    calc
      (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) =
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ ((w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)))))) := by
        duper [op_law]
      _ =
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ ((w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)))))))) := by
        duper [lemma_7]
      _ =
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ ((w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)))) ◇ ((((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w))) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)))))))))) := by
        duper [lemma_7]
      _ =
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w))))) := by
        duper [op_law]
      _ =
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ w) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)))) := by
        duper [lemma_7]
      _ = ((x ◇ ((y ◇ x) ◇ x)) ◇ z) := by
        duper [lemma_7]

  have lemma_9 (x y z : G) :
  (x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x)) = x := by
    calc
      (x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x)) =
        (x ◇ (((y ◇ ((z ◇ y) ◇ y)) ◇ x) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x))) := by
        duper [lemma_8]
      _ =
        (x ◇ (((y ◇ ((z ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ ((z ◇ y) ◇ y)) ◇ x) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x)))) := by
        duper [lemma_8]
      _ = x := by
        duper [op_law]

  have lemma_10 (x y z w : G) :
  (x ◇ (y ◇ ((z ◇ ((w ◇ z) ◇ z)) ◇ y))) = x := by
    duper [lemma_5, lemma_9]

  have lemma_11 (x y : G) :
  (x ◇ y) = x := by
    duper [lemma_10, lemma_9]

  show _ by
    exact lemma_11

