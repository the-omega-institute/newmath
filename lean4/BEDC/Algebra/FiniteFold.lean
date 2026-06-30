import BEDC.Algebra.Rel.Basic

namespace BEDC.Algebra.FiniteFold

open BEDC.Algebra.Rel

variable {A : Type u} {r : A -> A -> Prop}

inductive ListPairwiseRel (rel : A -> A -> Prop) : List A -> List A -> Prop where
  | nil : ListPairwiseRel rel [] []
  | cons {x y : A} {xs ys : List A} :
      rel x y -> ListPairwiseRel rel xs ys -> ListPairwiseRel rel (x :: xs) (y :: ys)

def listSum (R : RelCommRing A r) : List A -> A
  | [] => R.zero
  | x :: xs => R.add x (listSum R xs)

def listProd (R : RelCommRing A r) : List A -> A
  | [] => R.one
  | x :: xs => R.mul x (listProd R xs)

theorem append_assoc_clean {B : Type v} :
    ∀ xs ys zs : List B, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _ys, _zs =>
      rfl
  | x :: xs, ys, zs =>
      congrArg (List.cons x) (append_assoc_clean xs ys zs)

theorem reverseAux_append_clean {B : Type v} :
    ∀ xs acc : List B, List.reverseAux xs acc = xs.reverse ++ acc
  | [], _acc =>
      rfl
  | x :: xs, acc => by
      change List.reverseAux xs (x :: acc) = (List.reverseAux xs [x]) ++ acc
      rw [reverseAux_append_clean xs (x :: acc)]
      rw [reverseAux_append_clean xs [x]]
      exact (append_assoc_clean xs.reverse [x] acc).symm

theorem reverse_cons_clean {B : Type v} (x : B) (xs : List B) :
    (x :: xs).reverse = xs.reverse ++ [x] := by
  change List.reverseAux xs [x] = xs.reverse ++ [x]
  exact reverseAux_append_clean xs [x]

theorem sum_nil (R : RelCommRing A r) :
    r (listSum R []) R.zero :=
  R.refl R.zero

theorem sum_cons (R : RelCommRing A r) (x : A) (xs : List A) :
    r (listSum R (x :: xs)) (R.add x (listSum R xs)) :=
  R.refl (R.add x (listSum R xs))

theorem prod_nil (R : RelCommRing A r) :
    r (listProd R []) R.one :=
  R.refl R.one

theorem prod_cons (R : RelCommRing A r) (x : A) (xs : List A) :
    r (listProd R (x :: xs)) (R.mul x (listProd R xs)) :=
  R.refl (R.mul x (listProd R xs))

theorem sum_congr (R : RelCommRing A r) {xs ys : List A} :
    ListPairwiseRel r xs ys -> r (listSum R xs) (listSum R ys) := by
  intro paired
  induction paired with
  | nil =>
      exact R.refl R.zero
  | cons head tail ih =>
      exact R.add_congr head ih

theorem prod_congr (R : RelCommRing A r) {xs ys : List A} :
    ListPairwiseRel r xs ys -> r (listProd R xs) (listProd R ys) := by
  intro paired
  induction paired with
  | nil =>
      exact R.refl R.one
  | cons head tail ih =>
      exact R.mul_congr head ih

theorem sum_append (R : RelCommRing A r) :
    ∀ xs ys : List A, r (listSum R (xs ++ ys)) (R.add (listSum R xs) (listSum R ys))
  | [], ys =>
      R.symm (R.zero_add (listSum R ys))
  | x :: xs, ys => by
      have tail := sum_append R xs ys
      have step : r (R.add x (listSum R (xs ++ ys)))
          (R.add x (R.add (listSum R xs) (listSum R ys))) :=
        R.add_congr (R.refl x) tail
      exact R.trans step (R.symm (R.add_assoc x (listSum R xs) (listSum R ys)))

theorem prod_append (R : RelCommRing A r) :
    ∀ xs ys : List A, r (listProd R (xs ++ ys)) (R.mul (listProd R xs) (listProd R ys))
  | [], ys =>
      R.symm (R.one_mul (listProd R ys))
  | x :: xs, ys => by
      have tail := prod_append R xs ys
      have step : r (R.mul x (listProd R (xs ++ ys)))
          (R.mul x (R.mul (listProd R xs) (listProd R ys))) :=
        R.mul_congr (R.refl x) tail
      exact R.trans step (R.symm (R.mul_assoc x (listProd R xs) (listProd R ys)))

theorem sum_snoc (R : RelCommRing A r) :
    ∀ xs : List A, ∀ x : A,
      r (listSum R (xs ++ [x])) (R.add (listSum R xs) x)
  | [], x => by
      rw [List.nil_append]
      exact R.trans (R.add_zero x) (R.symm (R.zero_add x))
  | y :: ys, x => by
      have tail := sum_snoc R ys x
      have step : r (R.add y (listSum R (ys ++ [x])))
          (R.add y (R.add (listSum R ys) x)) :=
        R.add_congr (R.refl y) tail
      exact R.trans step (R.symm (R.add_assoc y (listSum R ys) x))

theorem prod_snoc (R : RelCommRing A r) :
    ∀ xs : List A, ∀ x : A,
      r (listProd R (xs ++ [x])) (R.mul (listProd R xs) x)
  | [], x => by
      rw [List.nil_append]
      exact R.trans (R.mul_one x) (R.symm (R.one_mul x))
  | y :: ys, x => by
      have tail := prod_snoc R ys x
      have step : r (R.mul y (listProd R (ys ++ [x])))
          (R.mul y (R.mul (listProd R ys) x)) :=
        R.mul_congr (R.refl y) tail
      exact R.trans step (R.symm (R.mul_assoc y (listProd R ys) x))

theorem sum_map (R : RelCommRing A r) {B : Type v}
    (f g : B -> A) :
    ∀ xs : List B, (∀ x : B, r (f x) (g x)) ->
      r (listSum R (List.map f xs)) (listSum R (List.map g xs))
  | [], _same =>
      R.refl R.zero
  | x :: xs, same => by
      exact R.add_congr (same x) (sum_map R f g xs same)

theorem prod_map (R : RelCommRing A r) {B : Type v}
    (f g : B -> A) :
    ∀ xs : List B, (∀ x : B, r (f x) (g x)) ->
      r (listProd R (List.map f xs)) (listProd R (List.map g xs))
  | [], _same =>
      R.refl R.one
  | x :: xs, same => by
      exact R.mul_congr (same x) (prod_map R f g xs same)

theorem sum_reverse (R : RelCommRing A r) :
    ∀ xs : List A, r (listSum R xs.reverse) (listSum R xs)
  | [] =>
      R.refl R.zero
  | x :: xs => by
      have reverseStep :
          r (listSum R ((x :: xs).reverse)) (R.add (listSum R xs.reverse) x) := by
        rw [reverse_cons_clean]
        exact sum_snoc R xs.reverse x
      have tail := sum_reverse R xs
      have movedTail :
          r (R.add (listSum R xs.reverse) x) (R.add (listSum R xs) x) :=
        R.add_congr tail (R.refl x)
      have commute : r (R.add (listSum R xs) x) (R.add x (listSum R xs)) :=
        R.add_comm (listSum R xs) x
      exact R.trans reverseStep (R.trans movedTail commute)

theorem prod_reverse (R : RelCommRing A r) :
    ∀ xs : List A, r (listProd R xs.reverse) (listProd R xs)
  | [] =>
      R.refl R.one
  | x :: xs => by
      have reverseStep :
          r (listProd R ((x :: xs).reverse)) (R.mul (listProd R xs.reverse) x) := by
        rw [reverse_cons_clean]
        exact prod_snoc R xs.reverse x
      have tail := prod_reverse R xs
      have movedTail :
          r (R.mul (listProd R xs.reverse) x) (R.mul (listProd R xs) x) :=
        R.mul_congr tail (R.refl x)
      have commute : r (R.mul (listProd R xs) x) (R.mul x (listProd R xs)) :=
        R.mul_comm (listProd R xs) x
      exact R.trans reverseStep (R.trans movedTail commute)

inductive ListPerm : List A -> List A -> Prop where
  | nil : ListPerm [] []
  | cons (x : A) {xs ys : List A} : ListPerm xs ys -> ListPerm (x :: xs) (x :: ys)
  | swap (x y : A) (xs : List A) : ListPerm (x :: y :: xs) (y :: x :: xs)
  | trans {xs ys zs : List A} : ListPerm xs ys -> ListPerm ys zs -> ListPerm xs zs

theorem listPerm_refl :
    ∀ xs : List A, ListPerm xs xs
  | [] =>
      ListPerm.nil
  | x :: xs =>
      ListPerm.cons x (listPerm_refl xs)

theorem listPerm_symm :
    ∀ {xs ys : List A}, ListPerm xs ys -> ListPerm ys xs
  | _, _, ListPerm.nil =>
      ListPerm.nil
  | _, _, ListPerm.cons x p =>
      ListPerm.cons x (listPerm_symm p)
  | _, _, ListPerm.swap x y xs =>
      ListPerm.swap y x xs
  | _, _, ListPerm.trans p q =>
      ListPerm.trans (listPerm_symm q) (listPerm_symm p)

theorem listPerm_append_left (zs : List A) :
    ∀ {xs ys : List A}, ListPerm xs ys -> ListPerm (zs ++ xs) (zs ++ ys)
  | xs, ys, p => by
      induction zs with
      | nil =>
          exact p
      | cons z zs ih =>
          exact ListPerm.cons z ih

theorem listPerm_append_right (zs : List A) :
    ∀ {xs ys : List A}, ListPerm xs ys -> ListPerm (xs ++ zs) (ys ++ zs)
  | _, _, ListPerm.nil =>
      listPerm_refl zs
  | _, _, ListPerm.cons x p =>
      ListPerm.cons x (listPerm_append_right zs p)
  | _, _, ListPerm.swap x y xs =>
      ListPerm.swap x y (xs ++ zs)
  | _, _, ListPerm.trans p q =>
      ListPerm.trans (listPerm_append_right zs p) (listPerm_append_right zs q)

theorem listPerm_snoc_cons (x : A) :
    ∀ xs : List A, ListPerm (xs ++ [x]) (x :: xs)
  | [] =>
      ListPerm.cons x ListPerm.nil
  | y :: ys =>
      ListPerm.trans
        (ListPerm.cons y (listPerm_snoc_cons x ys))
        (ListPerm.swap y x ys)

theorem listPerm_reverse :
    ∀ xs : List A, ListPerm xs xs.reverse
  | [] =>
      ListPerm.nil
  | x :: xs => by
      rw [reverse_cons_clean]
      exact ListPerm.trans
        (ListPerm.cons x (listPerm_reverse xs))
        (listPerm_symm (listPerm_snoc_cons x xs.reverse))

theorem listPerm_map {B : Type v} (f : A -> B) :
    ∀ {xs ys : List A}, ListPerm xs ys -> ListPerm (List.map f xs) (List.map f ys)
  | _, _, ListPerm.nil =>
      ListPerm.nil
  | _, _, ListPerm.cons x p =>
      ListPerm.cons (f x) (listPerm_map f p)
  | _, _, ListPerm.swap x y xs =>
      ListPerm.swap (f x) (f y) (List.map f xs)
  | _, _, ListPerm.trans p q =>
      ListPerm.trans (listPerm_map f p) (listPerm_map f q)

theorem sum_permInvariant (R : RelCommRing A r) :
    ∀ {xs ys : List A}, ListPerm xs ys -> r (listSum R xs) (listSum R ys)
  | _, _, ListPerm.nil =>
      R.refl R.zero
  | _, _, ListPerm.cons x p => by
      exact R.add_congr (R.refl x) (sum_permInvariant R p)
  | _, _, ListPerm.swap x y xs => by
      exact R.trans (R.symm (R.add_assoc x y (listSum R xs)))
        (R.trans (R.add_congr (R.add_comm x y) (R.refl (listSum R xs)))
          (R.add_assoc y x (listSum R xs)))
  | _, _, ListPerm.trans p q =>
      R.trans (sum_permInvariant R p) (sum_permInvariant R q)

theorem prod_permInvariant (R : RelCommRing A r) :
    ∀ {xs ys : List A}, ListPerm xs ys -> r (listProd R xs) (listProd R ys)
  | _, _, ListPerm.nil =>
      R.refl R.one
  | _, _, ListPerm.cons x p => by
      exact R.mul_congr (R.refl x) (prod_permInvariant R p)
  | _, _, ListPerm.swap x y xs => by
      exact R.trans (R.symm (R.mul_assoc x y (listProd R xs)))
        (R.trans (R.mul_congr (R.mul_comm x y) (R.refl (listProd R xs)))
          (R.mul_assoc y x (listProd R xs)))
  | _, _, ListPerm.trans p q =>
      R.trans (prod_permInvariant R p) (prod_permInvariant R q)

end BEDC.Algebra.FiniteFold
