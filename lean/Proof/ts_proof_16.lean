import Mathlib.Tactic.NthRewrite

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation650 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = x ◇ (y ◇ ((z ◇ x) ◇ y))

abbrev Equation448 (G : Type _) [Magma G] :=
  ∀ x y z : G, x = x ◇ (y ◇ (z ◇ (x ◇ z)))

theorem Equation650_implies_Equation448 (G : Type _) [Magma G]
    (op_law : Equation650 G) : Equation448 G :=
  have lemma1 (x y z w : G) :
      x ◇ ((y ◇ z) ◇ x) = (x ◇ ((y ◇ z) ◇ x)) ◇ (w ◇ (z ◇ w)) := by
    nth_rw 3 [op_law z x y]
    exact op_law (x ◇ ((y ◇ z) ◇ x)) w z

  have lemma2 (x y z w v u : G) :
      x ◇ ((y ◇ ((z ◇ w) ◇ y)) ◇ x) =
      (x ◇ ((y ◇ ((z ◇ w) ◇ y)) ◇ x)) ◇ (v ◇ ((u ◇ (w ◇ u)) ◇ v)) := by
    nth_rw 1 2 [lemma1 y z w u]
    exact lemma1 x (y ◇ ((z ◇ w) ◇ y)) (u ◇ (w ◇ u)) v

  have lemma3 (x y z w v : G) :
      x ◇ (y ◇ x) = (x ◇ (y ◇ x)) ◇ (z ◇ ((w ◇ ((v ◇ y) ◇ w)) ◇ z)) := by
    nth_rw 1 [lemma1 w v y x]
    exact op_law (x ◇ (y ◇ x)) z (w ◇ ((v ◇ y) ◇ w))

  have lemma4 (x y z w v : G) :
      x ◇ (y ◇ x) = (x ◇ (y ◇ x)) ◇ ((z ◇ (y ◇ z)) ◇ (w ◇ ((v ◇ y) ◇ w))) := by
    nth_rw 1 [lemma1 w v y z]
    exact lemma3 x y (z ◇ (y ◇ z)) w v

  have lemma5 (x y z w : G) :
      x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x) =
      (x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x)) ◇ (w ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ w)) := by
    nth_rw 1 [lemma2 w y z y x ((z ◇ y) ◇ y)]
    exact lemma4 x (y ◇ ((z ◇ y) ◇ y)) w x ((z ◇ y) ◇ y)

  have lemma6 (x y z w : G) :
      (x ◇ ((y ◇ x) ◇ x)) ◇ z =
      ((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ ((w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) ◇
        (z ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z))) := by
    nth_rw 1 [lemma5 z x y w]
    exact op_law ((x ◇ ((y ◇ x) ◇ x)) ◇ z) (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) z

  have lemma7 (x y z w : G) :
      (x ◇ ((y ◇ x) ◇ x)) ◇ z = ((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (w ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w)) := by
    nth_rw 1 [lemma5 w x y z]
    exact lemma6 x y z w

  have lemma8 (x y z : G) :
      (x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z) =
      ((x ◇ ((y ◇ x) ◇ x)) ◇
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (z ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z)))) ◇
      ((((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (z ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z))) ◇
        ((x ◇ ((y ◇ x) ◇ x)) ◇
          (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ (z ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z))))) := by
    let T := x ◇ ((y ◇ x) ◇ x)
    nth_rw 1 [lemma7 x y z z]
    exact lemma7 x y
      ((T ◇ z) ◇ (z ◇ (T ◇ z)))
      ((T ◇ z) ◇ (z ◇ (T ◇ z)))

  have lemma9 (x y z w : G) :
      ((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ w) = (x ◇ ((y ◇ x) ◇ x)) ◇ z := by
    let T := x ◇ ((y ◇ x) ◇ x)
    calc
      ((T ◇ z) ◇ (T ◇ w)) =
        ((T ◇ z) ◇ ((T ◇ w) ◇ ((T ◇ (T ◇ w)) ◇ ((w ◇ (T ◇ w)) ◇ (T ◇ (T ◇ w)))))) := by
        nth_rw 1 [←op_law]
      _ =
        ((T ◇ z) ◇ ((T ◇ w) ◇ ((T ◇ (T ◇ w)) ◇ ((w ◇ (T ◇ w)) ◇ ((T ◇ ((T ◇ w) ◇ (w ◇ (T ◇ w)))) ◇
            (((T ◇ w) ◇ (w ◇ (T ◇ w))) ◇ (T ◇ ((T ◇ w) ◇ (w ◇ (T ◇ w)))))))))) := by
        nth_rw 2 [lemma8 x y w]
      _ =
        ((T ◇ z) ◇ ((T ◇ w) ◇ ((T ◇ (T ◇ w)) ◇ (w ◇ (T ◇ w))))) := by
        nth_rw 1 [←op_law]
      _ = (T ◇ z) := by
        nth_rw 1 [←lemma7 x y (T ◇ w) w]
        symm
        exact lemma7 x y z (T ◇ w)

  have lemma10 (x y z : G) :
      ((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇
        (((x ◇ ((y ◇ x) ◇ x)) ◇ z) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ z)) =
      (x ◇ ((y ◇ x) ◇ x)) ◇ z := by
    nth_rw 1 [lemma9 x y z z]
    exact lemma9 x y z z

  have lemma11 (x y z : G) :
      x ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ x) = x := by
    symm
    nth_rw 1 [←lemma10 y z x]
    exact op_law x ((y ◇ ((z ◇ y) ◇ y)) ◇ x) (y ◇ ((z ◇ y) ◇ y))

  have lemma12 (x y z w : G) :
      x ◇ (y ◇ ((z ◇ ((w ◇ z) ◇ z)) ◇ y)) = x := by
    symm
    nth_rw 1 2 [←lemma11 x z w]
    exact lemma5 x z w y

  show _ by
    intros x y z
    symm
    nth_rw 1 [←lemma11 (y ◇ (z ◇ (x ◇ z))) x x]
    exact lemma12 x (y ◇ (z ◇ (x ◇ z))) x x
