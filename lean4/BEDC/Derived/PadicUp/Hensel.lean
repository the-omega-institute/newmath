import BEDC.Derived.PadicUp.FieldCore

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def ZpPoly (p : BHist) : Type :=
  List (ZpInt p)

def zpNatCoeff {p : BHist} (prime : NatPrime p) (n : Nat) : ZpInt p :=
  zpOfNat p prime (zpuNatToUnary n) (zpuNatToUnary_unary n)

def zpEval {p : BHist} : ZpPoly p -> ZpInt p -> ZpInt p
  | [], x => zpZero p x.prime
  | [c], _x => c
  | c :: d :: cs, x => zpAdd p c (zpMul p x (zpEval (d :: cs) x))

def zpPolyAdd {p : BHist} : ZpPoly p -> ZpPoly p -> ZpPoly p
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => zpAdd p x y :: zpPolyAdd xs ys

def zpPolyX {p : BHist} : ZpPoly p -> ZpPoly p
  | [] => []
  | c :: cs => zpZero p c.prime :: c :: cs

def zpDeriv {p : BHist} (f : ZpPoly p) : ZpPoly p :=
  match f with
  | [] => []
  | [_c] => []
  | _c :: d :: cs =>
      let tail := d :: cs
      zpPolyAdd tail (zpPolyX (zpDeriv tail))

def zpLinearPoly {p : BHist} (b m : ZpInt p) : ZpPoly p :=
  [b, m]

structure HenselData {p : BHist} (f : ZpPoly p) where
  a0 : ZpInt p
  root_mod_p :
    (zpLevel (zpEval f a0) (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty
  deriv_unit : ZpUnit (zpEval (zpDeriv f) a0)

def newtonStep {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) : ZpInt p :=
  zpSub p a (zpMul p (zpEval f a) (ZpUnitInv (zpEval (zpDeriv f) a) unit))

theorem ZpUnit_of_ZpEq {p : BHist} {x y : ZpInt p} :
    ZpEq x y -> ZpUnit y -> ZpUnit x := by
  intro same unit sameZero
  exact unit (hsame_trans (hsame_symm (same (BHist.e1 BHist.Empty)
    (unary_e1_closed unary_empty))) sameZero)

theorem zpAdd_rotate_middle {p : BHist} (a b c : ZpInt p) :
    ZpEq (zpAdd p (zpAdd p a b) c) (zpAdd p (zpAdd p a c) b) := by
  exact ZpEq_trans
    (zpAdd_assoc p a b c)
    (ZpEq_trans
      (zpAdd_congr (ZpEq_refl a) (zpAdd_comm p b c))
      (ZpEq_symm (zpAdd_assoc p a c b)))

theorem zpAdd_pair_swap {p : BHist} (a b c d : ZpInt p) :
    ZpEq (zpAdd p (zpAdd p a b) (zpAdd p c d))
      (zpAdd p (zpAdd p a c) (zpAdd p b d)) := by
  exact ZpEq_trans
    (ZpEq_symm (zpAdd_assoc p (zpAdd p a b) c d))
    (ZpEq_trans
      (zpAdd_congr (zpAdd_rotate_middle a b c) (ZpEq_refl d))
      (zpAdd_assoc p (zpAdd p a c) b d))

theorem zpAdd_pair_to_left_nested {p : BHist} (a b c d : ZpInt p) :
    ZpEq (zpAdd p (zpAdd p a b) (zpAdd p c d))
      (zpAdd p (zpAdd p a (zpAdd p b c)) d) := by
  exact ZpEq_trans
    (ZpEq_symm (zpAdd_assoc p (zpAdd p a b) c d))
    (zpAdd_congr (zpAdd_assoc p a b c) (ZpEq_refl d))

theorem zpAdd_left_nested_four {p : BHist} (a b c d : ZpInt p) :
    ZpEq (zpAdd p a (zpAdd p (zpAdd p b c) d))
      (zpAdd p (zpAdd p (zpAdd p a b) c) d) := by
  exact ZpEq_trans
    (ZpEq_symm (zpAdd_assoc p a (zpAdd p b c) d))
    (zpAdd_congr (ZpEq_symm (zpAdd_assoc p a b c)) (ZpEq_refl d))

theorem zpTaylor_linear_terms {p : BHist} (a delta H D : ZpInt p) :
    ZpEq
      (zpAdd p (zpMul p delta H) (zpMul p a (zpMul p D delta)))
      (zpMul p (zpAdd p H (zpMul p a D)) delta) := by
  exact ZpEq_trans
    (zpAdd_congr (zpMul_comm p delta H)
      (ZpEq_symm (zpMul_assoc p a D delta)))
    (ZpEq_symm (zpMul_add_distrib_right p H (zpMul p a D) delta))

theorem zpTaylor_quadratic_middle {p : BHist} (delta D : ZpInt p) :
    ZpEq (zpMul p delta (zpMul p D delta))
      (zpMul p (zpMul p delta delta) D) := by
  exact ZpEq_trans
    (zpMul_right_congr (zpMul_comm p D delta))
    (ZpEq_symm (zpMul_assoc p delta delta D))

theorem zpTaylor_square_factor_left {p : BHist} (A delta g : ZpInt p) :
    ZpEq (zpMul p A (zpMul p (zpMul p delta delta) g))
      (zpMul p (zpMul p delta delta) (zpMul p A g)) := by
  exact ZpEq_trans
    (zpMul_comm p A (zpMul p (zpMul p delta delta) g))
    (ZpEq_trans
      (zpMul_assoc p (zpMul p delta delta) g A)
      (zpMul_right_congr (zpMul_comm p g A)))

theorem zpTaylor_tail_ring {p : BHist} (a delta H D g : ZpInt p) :
    ZpEq
      (zpMul p (zpAdd p a delta)
        (zpAdd p (zpAdd p H (zpMul p D delta))
          (zpMul p (zpMul p delta delta) g)))
      (zpAdd p
        (zpAdd p (zpMul p a H)
          (zpMul p (zpAdd p H (zpMul p a D)) delta))
        (zpMul p (zpMul p delta delta)
          (zpAdd p D (zpMul p (zpAdd p a delta) g)))) := by
  let A := zpAdd p a delta
  let P := zpMul p delta delta
  let Ddelta := zpMul p D delta
  let linear := zpMul p (zpAdd p H (zpMul p a D)) delta
  let quad := zpMul p P D
  let Ag := zpMul p A g
  let Pg := zpMul p P g
  have outer :
      ZpEq
        (zpMul p A (zpAdd p (zpAdd p H Ddelta) Pg))
        (zpAdd p (zpMul p A (zpAdd p H Ddelta)) (zpMul p A Pg)) :=
    zpMul_add_distrib p A (zpAdd p H Ddelta) Pg
  have firstExpand :
      ZpEq
        (zpMul p A (zpAdd p H Ddelta))
        (zpAdd p (zpMul p A H) (zpMul p A Ddelta)) :=
    zpMul_add_distrib p A H Ddelta
  have aHExpand :
      ZpEq (zpMul p A H)
        (zpAdd p (zpMul p a H) (zpMul p delta H)) := by
    unfold A
    exact zpMul_add_distrib_right p a delta H
  have dExpand :
      ZpEq (zpMul p A Ddelta)
        (zpAdd p (zpMul p a Ddelta) (zpMul p delta Ddelta)) := by
    unfold A
    exact zpMul_add_distrib_right p a delta Ddelta
  have firstToExpanded :
      ZpEq
        (zpMul p A (zpAdd p H Ddelta))
        (zpAdd p
          (zpAdd p (zpMul p a H) (zpMul p delta H))
          (zpAdd p (zpMul p a Ddelta) (zpMul p delta Ddelta))) :=
    ZpEq_trans firstExpand (zpAdd_congr aHExpand dExpand)
  have expandedToCompact :
      ZpEq
        (zpAdd p
          (zpAdd p (zpMul p a H) (zpMul p delta H))
          (zpAdd p (zpMul p a Ddelta) (zpMul p delta Ddelta)))
        (zpAdd p (zpAdd p (zpMul p a H) linear) quad) := by
    exact ZpEq_trans
      (zpAdd_pair_to_left_nested (zpMul p a H) (zpMul p delta H)
        (zpMul p a Ddelta) (zpMul p delta Ddelta))
      (zpAdd_congr
        (zpAdd_congr (ZpEq_refl _)
          (by
            unfold linear Ddelta
            exact zpTaylor_linear_terms a delta H D))
        (by
          unfold quad P Ddelta
          exact zpTaylor_quadratic_middle delta D))
  have firstCompact :
      ZpEq (zpMul p A (zpAdd p H Ddelta))
        (zpAdd p (zpAdd p (zpMul p a H) linear) quad) :=
    ZpEq_trans firstToExpanded expandedToCompact
  have squareFactor :
      ZpEq (zpMul p A Pg) (zpMul p P Ag) := by
    unfold Pg P Ag A
    exact zpTaylor_square_factor_left (zpAdd p a delta) delta g
  have combineQuadratic :
      ZpEq
        (zpAdd p (zpAdd p (zpAdd p (zpMul p a H) linear) quad)
          (zpMul p P Ag))
        (zpAdd p (zpAdd p (zpMul p a H) linear)
          (zpMul p P (zpAdd p D Ag))) := by
    exact ZpEq_trans
      (zpAdd_assoc p (zpAdd p (zpMul p a H) linear) quad (zpMul p P Ag))
      (zpAdd_congr (ZpEq_refl _)
        (ZpEq_symm (zpMul_add_distrib p P D Ag)))
  exact ZpEq_trans outer
    (ZpEq_trans
      (zpAdd_congr firstCompact squareFactor)
      combineQuadratic)

theorem zpEval_poly_add {p : BHist} (f g : ZpPoly p) (x : ZpInt p) :
    ZpEq (zpEval (zpPolyAdd f g) x)
      (zpAdd p (zpEval f x) (zpEval g x)) := by
  induction f generalizing g with
  | nil =>
      cases g with
      | nil =>
          change ZpEq (zpZero p x.prime)
            (zpAdd p (zpZero p x.prime) (zpZero p x.prime))
          exact ZpEq_symm (zpZero_add_left p x.prime (zpZero p x.prime))
      | cons y ys =>
          change ZpEq (zpEval (y :: ys) x)
            (zpAdd p (zpZero p x.prime) (zpEval (y :: ys) x))
          exact ZpEq_symm (zpZero_add_left p x.prime (zpEval (y :: ys) x))
  | cons c cs ih =>
      cases g with
      | nil =>
          change ZpEq (zpEval (c :: cs) x)
            (zpAdd p (zpEval (c :: cs) x) (zpZero p x.prime))
          exact ZpEq_symm (zpZero_add_right p x.prime (zpEval (c :: cs) x))
      | cons d ds =>
          cases cs with
          | nil =>
              cases ds with
              | nil =>
                  change ZpEq (zpAdd p c d) (zpAdd p c d)
                  exact ZpEq_refl _
              | cons e es =>
                  change ZpEq
                    (zpAdd p (zpAdd p c d) (zpMul p x (zpEval (e :: es) x)))
                    (zpAdd p c
                      (zpAdd p d (zpMul p x (zpEval (e :: es) x))))
                  exact zpAdd_assoc p c d (zpMul p x (zpEval (e :: es) x))
          | cons e es =>
              cases ds with
              | nil =>
                  change ZpEq
                    (zpAdd p (zpAdd p c d) (zpMul p x (zpEval (e :: es) x)))
                    (zpAdd p (zpAdd p c (zpMul p x (zpEval (e :: es) x))) d)
                  exact zpAdd_rotate_middle c d (zpMul p x (zpEval (e :: es) x))
              | cons h hs =>
                  change ZpEq
                    (zpAdd p (zpAdd p c d)
                      (zpMul p x (zpEval (zpPolyAdd (e :: es) (h :: hs)) x)))
                    (zpAdd p (zpAdd p c (zpMul p x (zpEval (e :: es) x)))
                      (zpAdd p d (zpMul p x (zpEval (h :: hs) x))))
                  have tail :
                      ZpEq
                        (zpMul p x (zpEval (zpPolyAdd (e :: es) (h :: hs)) x))
                        (zpMul p x
                          (zpAdd p (zpEval (e :: es) x) (zpEval (h :: hs) x))) :=
                    zpMul_right_congr (ih (h :: hs))
                  exact ZpEq_trans
                    (zpAdd_congr (ZpEq_refl _) tail)
                    (ZpEq_trans
                      (zpAdd_congr (ZpEq_refl _)
                        (zpMul_add_distrib p x (zpEval (e :: es) x)
                          (zpEval (h :: hs) x)))
                      (zpAdd_pair_swap c d
                        (zpMul p x (zpEval (e :: es) x))
                        (zpMul p x (zpEval (h :: hs) x))))

theorem zpEval_poly_x {p : BHist} (f : ZpPoly p) (x : ZpInt p) :
    ZpEq (zpEval (zpPolyX f) x) (zpMul p x (zpEval f x)) := by
  cases f with
  | nil =>
      change ZpEq (zpZero p x.prime) (zpMul p x (zpZero p x.prime))
      exact ZpEq_symm (zpMul_zero_right p x)
  | cons c cs =>
      change ZpEq (zpAdd p (zpZero p c.prime) (zpMul p x (zpEval (c :: cs) x)))
        (zpMul p x (zpEval (c :: cs) x))
      exact zpZero_add_left p c.prime (zpMul p x (zpEval (c :: cs) x))

theorem zpEval_congr_arg {p : BHist} (f : ZpPoly p) {x y : ZpInt p} :
    ZpEq x y -> ZpEq (zpEval f x) (zpEval f y) := by
  intro same
  induction f with
  | nil =>
      exact ZpEq_refl _
  | cons c tail ih =>
      cases tail with
      | nil =>
          exact ZpEq_refl c
      | cons d ds =>
          change ZpEq
            (zpAdd p c (zpMul p x (zpEval (d :: ds) x)))
            (zpAdd p c (zpMul p y (zpEval (d :: ds) y)))
          exact zpAdd_congr (ZpEq_refl c)
            (zpMul_congr same ih)

theorem taylor_remainder {p : BHist} (f : ZpPoly p) (a delta : ZpInt p) :
    ∃ g : ZpInt p,
      ZpEq (zpEval f (zpAdd p a delta))
        (zpAdd p
          (zpAdd p (zpEval f a) (zpMul p (zpEval (zpDeriv f) a) delta))
          (zpMul p (zpMul p delta delta) g)) := by
  induction f with
  | nil =>
      exact ⟨zpZero p a.prime, by
        change ZpEq (zpZero p (zpAdd p a delta).prime)
          (zpAdd p
            (zpAdd p (zpZero p a.prime)
              (zpMul p (zpZero p a.prime) delta))
            (zpMul p (zpMul p delta delta) (zpZero p a.prime)))
        exact ZpEq_symm
          (ZpEq_trans
            (zpAdd_congr
              (ZpEq_trans
                (zpAdd_congr (ZpEq_refl _)
                  (zpMul_zero_left p a.prime delta))
                (zpZero_add_right p a.prime (zpZero p a.prime)))
              (zpMul_zero_right p (zpMul p delta delta)))
            (zpZero_add_right p a.prime (zpZero p a.prime)))⟩
  | cons c tail ih =>
      cases tail with
      | nil =>
          exact ⟨zpZero p c.prime, by
            change ZpEq c
              (zpAdd p (zpAdd p c (zpMul p (zpZero p a.prime) delta))
                (zpMul p (zpMul p delta delta) (zpZero p c.prime)))
            exact ZpEq_symm
              (ZpEq_trans
                (zpAdd_congr
                  (ZpEq_trans
                    (zpAdd_congr (ZpEq_refl c)
                      (zpMul_zero_left p a.prime delta))
                    (zpZero_add_right p a.prime c))
                  (zpMul_zero_right p (zpMul p delta delta)))
                (zpZero_add_right p c.prime c))⟩
      | cons d ds =>
          cases ih with
          | intro g hg =>
              let H := zpEval (d :: ds) a
              let D := zpEval (zpDeriv (d :: ds)) a
              let P := zpMul p delta delta
              let nextG := zpAdd p D (zpMul p (zpAdd p a delta) g)
              have tailAt :
                  ZpEq (zpEval (d :: ds) (zpAdd p a delta))
                    (zpAdd p (zpAdd p H (zpMul p D delta)) (zpMul p P g)) :=
                hg
              have derivAt :
                  ZpEq (zpEval (zpDeriv (c :: d :: ds)) a)
                    (zpAdd p H (zpMul p a D)) := by
                change ZpEq (zpEval (zpPolyAdd (d :: ds)
                    (zpPolyX (zpDeriv (d :: ds)))) a)
                  (zpAdd p H (zpMul p a D))
                exact ZpEq_trans
                  (zpEval_poly_add (d :: ds) (zpPolyX (zpDeriv (d :: ds))) a)
                  (zpAdd_congr (ZpEq_refl H) (zpEval_poly_x (zpDeriv (d :: ds)) a))
              exact ⟨nextG, by
                change ZpEq
                  (zpAdd p c
                    (zpMul p (zpAdd p a delta)
                      (zpEval (d :: ds) (zpAdd p a delta))))
                  (zpAdd p
                    (zpAdd p
                      (zpAdd p c (zpMul p a H))
                      (zpMul p (zpEval (zpDeriv (c :: d :: ds)) a) delta))
                    (zpMul p P nextG))
                have replaceTail :
                    ZpEq
                      (zpAdd p c
                        (zpMul p (zpAdd p a delta)
                          (zpEval (d :: ds) (zpAdd p a delta))))
                      (zpAdd p c
                        (zpMul p (zpAdd p a delta)
                          (zpAdd p (zpAdd p H (zpMul p D delta))
                            (zpMul p P g)))) :=
                  zpAdd_congr (ZpEq_refl c) (zpMul_right_congr tailAt)
                have ringStep :
                    ZpEq
                      (zpAdd p c
                        (zpMul p (zpAdd p a delta)
                          (zpAdd p (zpAdd p H (zpMul p D delta))
                            (zpMul p P g))))
                      (zpAdd p c
                        (zpAdd p
                          (zpAdd p (zpMul p a H)
                            (zpMul p (zpAdd p H (zpMul p a D)) delta))
                          (zpMul p P nextG))) :=
                  zpAdd_congr (ZpEq_refl c) (zpTaylor_tail_ring a delta H D g)
                have pack :
                    ZpEq
                      (zpAdd p c
                        (zpAdd p
                          (zpAdd p (zpMul p a H)
                            (zpMul p (zpAdd p H (zpMul p a D)) delta))
                          (zpMul p P nextG)))
                      (zpAdd p
                        (zpAdd p
                          (zpAdd p c (zpMul p a H))
                          (zpMul p (zpAdd p H (zpMul p a D)) delta))
                        (zpMul p P nextG)) := by
                  exact zpAdd_left_nested_four c (zpMul p a H)
                    (zpMul p (zpAdd p H (zpMul p a D)) delta)
                    (zpMul p P nextG)
                exact ZpEq_trans replaceTail
                  (ZpEq_trans ringStep
                    (ZpEq_trans pack
                      (zpAdd_congr
                        (zpAdd_congr (ZpEq_refl _)
                          (zpMul_left_congr (ZpEq_symm derivAt)))
                        (ZpEq_refl _))))⟩

theorem zpSub_self_cancel_left {p : BHist} (x y : ZpInt p) :
    ZpEq (zpAdd p x (zpSub p y x)) y :=
  zpAdd_sub_cancel x y

theorem newton_delta_eq_neg {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) :
    ZpEq (zpSub p (newtonStep f a unit) a)
      (zpNeg p (zpMul p (zpEval f a)
        (ZpUnitInv (zpEval (zpDeriv f) a) unit))) := by
  unfold newtonStep
  unfold zpSub
  let q := zpMul p (zpEval f a) (ZpUnitInv (zpEval (zpDeriv f) a) unit)
  have assoc :
      ZpEq (zpAdd p (zpAdd p a (zpNeg p q)) (zpNeg p a))
        (zpAdd p a (zpAdd p (zpNeg p q) (zpNeg p a))) :=
    zpAdd_assoc p a (zpNeg p q) (zpNeg p a)
  have commute :
      ZpEq (zpAdd p (zpNeg p q) (zpNeg p a))
        (zpAdd p (zpNeg p a) (zpNeg p q)) :=
    zpAdd_comm p (zpNeg p q) (zpNeg p a)
  have assocBack :
      ZpEq (zpAdd p a (zpAdd p (zpNeg p a) (zpNeg p q)))
        (zpAdd p (zpAdd p a (zpNeg p a)) (zpNeg p q)) :=
    ZpEq_symm (zpAdd_assoc p a (zpNeg p a) (zpNeg p q))
  exact ZpEq_trans assoc
    (ZpEq_trans (zpAdd_congr (ZpEq_refl a) commute)
      (ZpEq_trans assocBack
        (ZpEq_trans
          (zpAdd_congr (zpAdd_neg_right p a) (ZpEq_refl (zpNeg p q)))
          (zpZero_add_left p a.prime (zpNeg p q)))))

theorem newton_d_times_q {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) :
    let fa := zpEval f a
    let d := zpEval (zpDeriv f) a
    let dinv := ZpUnitInv d unit
    ZpEq (zpMul p d (zpMul p fa dinv)) fa := by
  let fa := zpEval f a
  let d := zpEval (zpDeriv f) a
  let dinv := ZpUnitInv d unit
  have assocForward :
      ZpEq (zpMul p d (zpMul p fa dinv))
        (zpMul p (zpMul p d fa) dinv) :=
    ZpEq_symm (zpMul_assoc p d fa dinv)
  have commuteLeft :
      ZpEq (zpMul p (zpMul p d fa) dinv)
        (zpMul p (zpMul p fa d) dinv) :=
    zpMul_left_congr (zpMul_comm p d fa)
  have assocBack :
      ZpEq (zpMul p (zpMul p fa d) dinv)
        (zpMul p fa (zpMul p d dinv)) :=
    zpMul_assoc p fa d dinv
  exact ZpEq_trans assocForward
    (ZpEq_trans commuteLeft
      (ZpEq_trans assocBack
        (ZpEq_trans (zpMul_right_congr (ZpUnitInv_mul d unit))
          (zpOne_mul_right p fa.prime fa))))

theorem newton_linear_cancel {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) :
    ZpEq
      (zpAdd p (zpEval f a)
        (zpMul p (zpEval (zpDeriv f) a)
          (zpSub p (newtonStep f a unit) a)))
      (zpZero p (zpEval f a).prime) := by
  let fa := zpEval f a
  let d := zpEval (zpDeriv f) a
  let dinv := ZpUnitInv d unit
  let q := zpMul p fa dinv
  have delta :
      ZpEq (zpSub p (newtonStep f a unit) a) (zpNeg p q) :=
    newton_delta_eq_neg f a unit
  have replace :
      ZpEq (zpMul p d (zpSub p (newtonStep f a unit) a))
        (zpMul p d (zpNeg p q)) :=
    zpMul_right_congr delta
  have negTerm :
      ZpEq (zpMul p d (zpNeg p q)) (zpNeg p fa) := by
    apply zpAdd_cancel_right (z := zpMul p d q)
    have rightZero :
        ZpEq (zpAdd p (zpNeg p fa) (zpMul p d q))
          (zpZero p fa.prime) := by
      exact ZpEq_trans
        (zpAdd_congr (ZpEq_refl (zpNeg p fa))
          (newton_d_times_q f a unit))
        (zpAdd_neg_left p fa)
    have leftZero :
        ZpEq (zpAdd p (zpMul p d (zpNeg p q)) (zpMul p d q))
          (zpZero p d.prime) := by
      have combine :
          ZpEq (zpAdd p (zpMul p d (zpNeg p q)) (zpMul p d q))
            (zpMul p d (zpAdd p (zpNeg p q) q)) :=
        ZpEq_symm (zpMul_add_distrib p d (zpNeg p q) q)
      exact ZpEq_trans combine
        (ZpEq_trans (zpMul_right_congr (zpAdd_neg_left p q))
          (zpMul_zero_right p d))
    exact ZpEq_trans leftZero
      (ZpEq_symm (ZpEq_trans rightZero
        (zpZero_prime_irrel fa.prime d.prime)))
  exact ZpEq_trans
    (zpAdd_congr (ZpEq_refl fa)
      (ZpEq_trans replace negTerm))
    (zpAdd_neg_right p fa)

theorem newton_step_as_add_delta {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) :
    ZpEq (newtonStep f a unit)
      (zpAdd p a (zpSub p (newtonStep f a unit) a)) := by
  exact ZpEq_symm (zpAdd_sub_cancel a (newtonStep f a unit))

theorem newton_step_residual_square {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) :
    ∃ g : ZpInt p,
      ZpEq (zpEval f (newtonStep f a unit))
        (zpMul p
          (zpMul p (zpSub p (newtonStep f a unit) a)
            (zpSub p (newtonStep f a unit) a))
          g) := by
  let delta := zpSub p (newtonStep f a unit) a
  cases taylor_remainder f a delta with
  | intro g tg =>
      have stepReplace :
          ZpEq (zpEval f (newtonStep f a unit))
            (zpEval f (zpAdd p a delta)) := by
        exact zpEval_congr_arg f (newton_step_as_add_delta f a unit)
      have collapse :
          ZpEq
            (zpAdd p
              (zpAdd p (zpEval f a)
                (zpMul p (zpEval (zpDeriv f) a) delta))
              (zpMul p (zpMul p delta delta) g))
            (zpMul p (zpMul p delta delta) g) := by
        exact ZpEq_trans
          (zpAdd_congr (newton_linear_cancel f a unit) (ZpEq_refl _))
          (zpZero_add_left p (zpEval f a).prime (zpMul p (zpMul p delta delta) g))
      exact ⟨g, ZpEq_trans stepReplace (ZpEq_trans tg collapse)⟩

theorem NatMul_unit_left_closed_local {q : BHist} :
    UnaryHistory q -> NatMul NatOne q q := by
  intro qUnary
  induction q with
  | Empty =>
      exact NatMul.zero (unary_e1_closed unary_empty)
  | e0 q =>
      cases qUnary
  | e1 q ih =>
      exact NatMul.succ (ih qUnary) (cont_intro rfl)

theorem PDvdNat_zero_exponent {p n : BHist}
    (prime : NatPrime p) (nUnary : UnaryHistory n) :
    PDvdNat p (zpuNatToUnary 0) n := by
  change PDvdNat p BHist.Empty n
  exact ⟨NatOne, PPow.zero prime.left,
    ⟨n, nUnary, NatMul_unit_left_closed_local nUnary⟩⟩

theorem zpLevel_zero_to_PDvd_same {p : BHist} (a : ZpInt p)
    (k : Nat)
    (zeroK : (zpLevel a (zpuNatToUnary k) (zpuNatToUnary_unary k)).val =
      BHist.Empty) :
    PDvdNat p (zpuNatToUnary k)
      (a.trunc (zpuNatToUnary k) (zpuNatToUnary_unary k)).val := by
  have raw := zpLevel_zero_ext_PDvdNat a
    (zpuNatToUnary_unary k) (zpuNatToUnary_unary 0) zeroK
  change PDvdNat p (zpuNatToUnary k)
    (a.trunc (BEDC.FKernel.Cont.append (zpuNatToUnary k) (zpuNatToUnary 0))
      (unary_append_closed (zpuNatToUnary_unary k) (zpuNatToUnary_unary 0))).val at raw
  have sameLevel :
      hsame (BEDC.FKernel.Cont.append (zpuNatToUnary k) (zpuNatToUnary 0))
        (zpuNatToUnary k) := by
    exact append_empty_right (zpuNatToUnary k)
  exact PDvdNat_hsame_exponent_result raw (hsame_refl _)
    (zpTrunc_level_hsame a
      (unary_append_closed (zpuNatToUnary_unary k) (zpuNatToUnary_unary 0))
      (zpuNatToUnary_unary k) sameLevel)

theorem zpMul_level_empty_of_left_level {p : BHist} (x y : ZpInt p)
    (k : Nat)
    (zeroX : (zpLevel x (zpuNatToUnary k) (zpuNatToUnary_unary k)).val =
      BHist.Empty) :
    (zpLevel (zpMul p x y) (zpuNatToUnary k) (zpuNatToUnary_unary k)).val =
      BHist.Empty := by
  have left : PDvdNat p (zpuNatToUnary k)
      ((x.trunc (zpuNatToUnary k) (zpuNatToUnary_unary k)).val) :=
    zpLevel_zero_to_PDvd_same x k zeroX
  have right : PDvdNat p (zpuNatToUnary 0)
      ((y.trunc (zpuNatToUnary k) (zpuNatToUnary_unary k)).val) :=
    PDvdNat_zero_exponent y.prime
      (BoundedNat_unary (pPowCanon_unary p (zpuNatToUnary k))
        (y.trunc (zpuNatToUnary k) (zpuNatToUnary_unary k)))
  have add : NatAdd (zpuNatToUnary k) (zpuNatToUnary 0) (zpuNatToUnary k) :=
    ⟨zpuNatToUnary_unary k, zpuNatToUnary_unary 0,
      cont_intro (append_empty_right (zpuNatToUnary k))⟩
  exact zpMul_level_empty_of_PDvdNat_product x y (zpuNatToUnary_unary k)
    add left right

theorem ZpEq_level_empty_transport_local {p N : BHist} {x y : ZpInt p}
    (NUnary : UnaryHistory N) :
    ZpEq x y ->
      (zpLevel y N NUnary).val = BHist.Empty ->
        (zpLevel x N NUnary).val = BHist.Empty := by
  intro same yZero
  exact hsame_trans (same N NUnary) yZero

theorem newton_delta_level_zero {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) (k : Nat)
    (faZero : (zpLevel (zpEval f a) (zpuNatToUnary k)
      (zpuNatToUnary_unary k)).val = BHist.Empty) :
    (zpLevel (zpSub p (newtonStep f a unit) a) (zpuNatToUnary k)
      (zpuNatToUnary_unary k)).val = BHist.Empty := by
  let fa := zpEval f a
  let d := zpEval (zpDeriv f) a
  let dinv := ZpUnitInv d unit
  have qZero :
      (zpLevel (zpMul p fa dinv) (zpuNatToUnary k)
        (zpuNatToUnary_unary k)).val = BHist.Empty :=
    zpMul_level_empty_of_left_level fa dinv k faZero
  have deltaEq :
      ZpEq (zpSub p (newtonStep f a unit) a)
        (zpNeg p (zpMul p fa dinv)) :=
    newton_delta_eq_neg f a unit
  have negZero :
      (zpLevel (zpNeg p (zpMul p fa dinv)) (zpuNatToUnary k)
        (zpuNatToUnary_unary k)).val = BHist.Empty := by
    have addDrop :
        hsame ((zpAdd p (zpNeg p (zpMul p fa dinv)) (zpMul p fa dinv)).trunc
          (zpuNatToUnary k) (zpuNatToUnary_unary k)).val
          ((zpNeg p (zpMul p fa dinv)).trunc
            (zpuNatToUnary k) (zpuNatToUnary_unary k)).val :=
      zpAdd_level_zero_right (zpNeg p (zpMul p fa dinv)) (zpMul p fa dinv)
        (zpuNatToUnary_unary k) qZero
    have addZero :
        hsame ((zpAdd p (zpNeg p (zpMul p fa dinv)) (zpMul p fa dinv)).trunc
          (zpuNatToUnary k) (zpuNatToUnary_unary k)).val
          ((zpZero p (zpMul p fa dinv).prime).trunc
            (zpuNatToUnary k) (zpuNatToUnary_unary k)).val :=
      zpAdd_neg_left p (zpMul p fa dinv) (zpuNatToUnary k) (zpuNatToUnary_unary k)
    exact hsame_trans (hsame_symm addDrop) addZero
  exact ZpEq_level_empty_transport_local (zpuNatToUnary_unary k) deltaEq negZero

theorem newton_step_lifts {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) (k : Nat)
    (faZero : (zpLevel (zpEval f a) (zpuNatToUnary k)
      (zpuNatToUnary_unary k)).val = BHist.Empty) :
    (zpLevel (zpEval f (newtonStep f a unit)) (zpuNatToUnary (k + k))
      (zpuNatToUnary_unary (k + k))).val = BHist.Empty := by
  cases newton_step_residual_square f a unit with
  | intro g residual =>
      let delta := zpSub p (newtonStep f a unit) a
      let N := zpuNatToUnary (k + k)
      have NUnary : UnaryHistory N := zpuNatToUnary_unary (k + k)
      have deltaZero :
          (zpLevel delta (zpuNatToUnary k) (zpuNatToUnary_unary k)).val =
            BHist.Empty :=
        newton_delta_level_zero f a unit k faZero
      have leftRaw : PDvdNat p (zpuNatToUnary k)
          (delta.trunc N NUnary).val := by
        have appendSame :
            hsame (BEDC.FKernel.Cont.append (zpuNatToUnary k) (zpuNatToUnary k)) N :=
          zpuNatToUnary_add_hsame k k
        have raw := zpLevel_zero_ext_PDvdNat delta
          (zpuNatToUnary_unary k) (zpuNatToUnary_unary k) deltaZero
        exact PDvdNat_hsame_exponent_result raw (hsame_refl _)
          (zpTrunc_level_hsame delta
            (unary_append_closed (zpuNatToUnary_unary k) (zpuNatToUnary_unary k))
            NUnary appendSame)
      have squareZero :
          (zpLevel (zpMul p delta delta) N NUnary).val = BHist.Empty := by
        exact zpMul_level_empty_of_PDvdNat_product delta delta NUnary
          (zpuNatToUnary_natAdd k k) leftRaw leftRaw
      have squareTimesZero :
          (zpLevel (zpMul p (zpMul p delta delta) g) N NUnary).val =
            BHist.Empty :=
        zpMul_level_empty_of_left_level (zpMul p delta delta) g (k + k)
          squareZero
      exact ZpEq_level_empty_transport_local NUnary residual squareTimesZero

theorem zpEval_linear {p : BHist} (b m x : ZpInt p) :
    ZpEq (zpEval (zpLinearPoly b m) x) (zpAdd p b (zpMul p x m)) := by
  exact ZpEq_refl _

theorem zpDeriv_linear {p : BHist} (b m : ZpInt p) :
    zpDeriv (zpLinearPoly b m) = [m] := by
  rfl

theorem zpNatCoeff_one_mul {p : BHist} (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpMul p (zpNatCoeff prime 1) x) x := by
  unfold zpNatCoeff
  exact zpOne_mul_left p prime x

theorem zpEval_deriv_linear {p : BHist} (b m x : ZpInt p) :
    ZpEq (zpEval (zpDeriv (zpLinearPoly b m)) x) m := by
  exact ZpEq_refl m

def linearHenselUnit {p : BHist} (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpUnit (zpEval (zpDeriv (zpLinearPoly b m)) a0) :=
  ZpUnit_of_ZpEq (zpEval_deriv_linear b m a0) unit

def linearHenselRoot {p : BHist} (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpInt p :=
  newtonStep (zpLinearPoly b m) a0 (linearHenselUnit b m a0 unit)

theorem zpSub_self_eq_zero {p : BHist} (x : ZpInt p) :
    ZpEq (zpSub p x x) (zpZero p x.prime) := by
  unfold zpSub
  exact zpAdd_neg_right p x

theorem zpNeg_congr {p : BHist} {x y : ZpInt p} :
    ZpEq x y -> ZpEq (zpNeg p x) (zpNeg p y) := by
  intro same
  intro N NUnary
  unfold zpNeg zpNegTrunc fromNatModPow natMod
  exact natModFn_hsame_arg_transport (M := pPowCanon p N)
    (natComplementMod_hsame_arg_transport (same N NUnary))

theorem zpSub_congr {p : BHist} {x x' y y' : ZpInt p} :
    ZpEq x x' -> ZpEq y y' -> ZpEq (zpSub p x y) (zpSub p x' y') := by
  intro sameX sameY
  unfold zpSub
  exact zpAdd_congr sameX (zpNeg_congr sameY)

theorem linearHenselRoot_mul_slope {p : BHist}
    (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpEq (zpMul p (linearHenselRoot b m a0 unit) m)
      (zpSub p (zpMul p a0 m) (zpAdd p b (zpMul p a0 m))) := by
  let d := zpEval (zpDeriv (zpLinearPoly b m)) a0
  let dinv := ZpUnitInv d (linearHenselUnit b m a0 unit)
  let fa := zpAdd p b (zpMul p a0 m)
  have rootUnfold :
      ZpEq (linearHenselRoot b m a0 unit)
        (zpSub p a0 (zpMul p fa dinv)) := by
    unfold linearHenselRoot newtonStep
    exact zpSub_congr (ZpEq_refl a0)
      (zpMul_left_congr (zpEval_linear b m a0))
  have mulRoot :
      ZpEq (zpMul p (linearHenselRoot b m a0 unit) m)
        (zpMul p (zpSub p a0 (zpMul p fa dinv)) m) :=
    zpMul_left_congr rootUnfold
  have subTail :
      ZpEq (zpMul p (zpSub p a0 (zpMul p fa dinv)) m)
        (zpSub p (zpMul p a0 m) (zpMul p (zpMul p fa dinv) m)) := by
    apply zpAdd_cancel_right (z := zpMul p (zpMul p fa dinv) m)
    have tailComm :
        ZpEq (zpMul p (zpMul p fa dinv) m) (zpMul p m (zpMul p fa dinv)) :=
      zpMul_comm p (zpMul p fa dinv) m
    exact ZpEq_trans
      (ZpEq_trans
        (zpAdd_congr (ZpEq_refl _ ) tailComm)
        (zpSub_mul_add_tail (zpMul p fa dinv) a0 m))
      (ZpEq_symm (zpSub_add_cancel
        (zpMul p (zpMul p fa dinv) m) (zpMul p a0 m)))
  have invTerm :
      ZpEq (zpMul p (zpMul p fa dinv) m) fa := by
    have assoc1 :
        ZpEq (zpMul p (zpMul p fa dinv) m)
          (zpMul p fa (zpMul p dinv m)) :=
      zpMul_assoc p fa dinv m
    have rightInv :
        ZpEq (zpMul p dinv m) (zpOne p d.prime) := by
      exact ZpEq_trans (zpMul_right_congr (ZpEq_symm (zpEval_deriv_linear b m a0)))
        (ZpUnitInv_mul_right d (linearHenselUnit b m a0 unit))
    exact ZpEq_trans assoc1
      (ZpEq_trans (zpMul_right_congr rightInv)
        (zpOne_mul_right p fa.prime fa))
  exact ZpEq_trans mulRoot
    (ZpEq_trans subTail (zpSub_congr (ZpEq_refl _) invTerm))

theorem linearHenselRoot_is_root {p : BHist}
    (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpEq (zpEval (zpLinearPoly b m) (linearHenselRoot b m a0 unit))
      (zpZero p b.prime) := by
  let fa := zpAdd p b (zpMul p a0 m)
  let r := linearHenselRoot b m a0 unit
  have evalR :
      ZpEq (zpEval (zpLinearPoly b m) r) (zpAdd p b (zpMul p r m)) :=
    zpEval_linear b m r
  have rootMul := linearHenselRoot_mul_slope b m a0 unit
  have replaceMul :
      ZpEq (zpAdd p b (zpMul p r m))
        (zpAdd p b (zpSub p (zpMul p a0 m) fa)) :=
    zpAdd_congr (ZpEq_refl b) rootMul
  have commuteInside :
      ZpEq (zpAdd p b (zpSub p (zpMul p a0 m) fa))
        (zpAdd p (zpSub p (zpMul p a0 m) fa) b) :=
    zpAdd_comm p b (zpSub p (zpMul p a0 m) fa)
  have addBack :
      ZpEq (zpAdd p (zpSub p (zpMul p a0 m) fa) b)
        (zpSub p (zpMul p a0 m) (zpMul p a0 m)) := by
    apply zpAdd_cancel_right (z := zpMul p a0 m)
    have leftAssoc :
        ZpEq
          (zpAdd p
            (zpAdd p (zpSub p (zpMul p a0 m) fa) b)
            (zpMul p a0 m))
          (zpAdd p (zpSub p (zpMul p a0 m) fa)
            (zpAdd p b (zpMul p a0 m))) :=
      zpAdd_assoc p (zpSub p (zpMul p a0 m) fa) b (zpMul p a0 m)
    have closeLeft :
        ZpEq
          (zpAdd p (zpSub p (zpMul p a0 m) fa)
            (zpAdd p b (zpMul p a0 m)))
          (zpMul p a0 m) :=
      ZpEq_trans (zpAdd_congr (ZpEq_refl _)
        (ZpEq_symm (ZpEq_refl fa)))
        (zpSub_add_cancel fa (zpMul p a0 m))
    have rightCancel :
        ZpEq
          (zpAdd p (zpSub p (zpMul p a0 m) (zpMul p a0 m))
            (zpMul p a0 m))
          (zpMul p a0 m) :=
      zpSub_add_cancel (zpMul p a0 m) (zpMul p a0 m)
    exact ZpEq_trans leftAssoc
      (ZpEq_trans closeLeft (ZpEq_symm rightCancel))
  exact ZpEq_trans evalR
    (ZpEq_trans replaceMul
      (ZpEq_trans commuteInside
        (ZpEq_trans addBack (zpSub_self_eq_zero (zpMul p a0 m)))))

end BEDC.Derived.PadicUp
