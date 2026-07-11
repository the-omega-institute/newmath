import BEDC.Derived.RHRoute.IntervalMatrixPSD

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Derived.RationalUp

structure QInterval where
  lo : Rat
  hi : Rat

def InInterval (x : Rat) (I : QInterval) : Prop :=
  ratLe I.lo x ∧ ratLe x I.hi

def singletonInterval (x : Rat) : QInterval :=
  { lo := x, hi := x }

def intervalAdd (A B : QInterval) : QInterval :=
  { lo := ratAdd A.lo B.lo
    hi := ratAdd A.hi B.hi }

def intervalMul (A B : QInterval) : QInterval :=
  let p00 := ratMul A.lo B.lo
  let p01 := ratMul A.lo B.hi
  let p10 := ratMul A.hi B.lo
  let p11 := ratMul A.hi B.hi
  { lo := min4 p00 p01 p10 p11
    hi := max4 p00 p01 p10 p11 }

theorem intervalAdd_encloses {A B : QInterval} {x y : Rat} :
    InInterval x A -> InInterval y B ->
      InInterval (ratAdd x y) (intervalAdd A B) := by
  intro hx hy
  constructor
  · exact BEDC.Real.RatNumKernel.ratAdd_le_add hx.left hy.left
  · exact BEDC.Real.RatNumKernel.ratAdd_le_add hx.right hy.right

private theorem intervalMul_upper
    {alo ahi blo bhi x y : Rat}
    (hxlo : ratLe alo x)
    (hxhi : ratLe x ahi)
    (hylo : ratLe blo y)
    (hyhi : ratLe y bhi) :
    ratLe (ratMul x y)
      (max4
        (ratMul alo blo) (ratMul alo bhi)
        (ratMul ahi blo) (ratMul ahi bhi)) := by
  cases ratLe_total ratZero y with
  | inl yNonneg =>
      have xToHi : ratLe (ratMul x y) (ratMul ahi y) :=
        ratMul_le_mul_right hxhi yNonneg
      cases ratLe_total ratZero ahi with
      | inl ahiNonneg =>
          have hiToCorner :
              ratLe (ratMul ahi y) (ratMul ahi bhi) :=
            ratMul_le_mul_left hyhi ahiNonneg
          exact ratLe_trans xToHi
            (ratLe_trans hiToCorner
              (fourth_le_max4
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi)))
      | inr ahiNonpos =>
          have hiToCorner :
              ratLe (ratMul ahi y) (ratMul ahi blo) :=
            ratMul_le_mul_left_nonpos hylo ahiNonpos
          exact ratLe_trans xToHi
            (ratLe_trans hiToCorner
              (third_le_max4
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi)))
  | inr yNonpos =>
      have xToLo : ratLe (ratMul x y) (ratMul alo y) :=
        ratMul_le_mul_right_nonpos hxlo yNonpos
      cases ratLe_total ratZero alo with
      | inl aloNonneg =>
          have loToCorner :
              ratLe (ratMul alo y) (ratMul alo bhi) :=
            ratMul_le_mul_left hyhi aloNonneg
          exact ratLe_trans xToLo
            (ratLe_trans loToCorner
              (second_le_max4
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi)))
      | inr aloNonpos =>
          have loToCorner :
              ratLe (ratMul alo y) (ratMul alo blo) :=
            ratMul_le_mul_left_nonpos hylo aloNonpos
          exact ratLe_trans xToLo
            (ratLe_trans loToCorner
              (first_le_max4
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi)))

private theorem intervalMul_lower
    {alo ahi blo bhi x y : Rat}
    (hxlo : ratLe alo x)
    (hxhi : ratLe x ahi)
    (hylo : ratLe blo y)
    (hyhi : ratLe y bhi) :
    ratLe
      (min4
        (ratMul alo blo) (ratMul alo bhi)
        (ratMul ahi blo) (ratMul ahi bhi))
      (ratMul x y) := by
  cases ratLe_total ratZero y with
  | inl yNonneg =>
      have loToX : ratLe (ratMul alo y) (ratMul x y) :=
        ratMul_le_mul_right hxlo yNonneg
      cases ratLe_total ratZero alo with
      | inl aloNonneg =>
          have cornerToLo :
              ratLe (ratMul alo blo) (ratMul alo y) :=
            ratMul_le_mul_left hylo aloNonneg
          exact ratLe_trans
            (ratLe_trans
              (min4_le_first
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi))
              cornerToLo)
            loToX
      | inr aloNonpos =>
          have cornerToLo :
              ratLe (ratMul alo bhi) (ratMul alo y) :=
            ratMul_le_mul_left_nonpos hyhi aloNonpos
          exact ratLe_trans
            (ratLe_trans
              (min4_le_second
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi))
              cornerToLo)
            loToX
  | inr yNonpos =>
      have hiToX : ratLe (ratMul ahi y) (ratMul x y) :=
        ratMul_le_mul_right_nonpos hxhi yNonpos
      cases ratLe_total ratZero ahi with
      | inl ahiNonneg =>
          have cornerToHi :
              ratLe (ratMul ahi blo) (ratMul ahi y) :=
            ratMul_le_mul_left hylo ahiNonneg
          exact ratLe_trans
            (ratLe_trans
              (min4_le_third
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi))
              cornerToHi)
            hiToX
      | inr ahiNonpos =>
          have cornerToHi :
              ratLe (ratMul ahi bhi) (ratMul ahi y) :=
            ratMul_le_mul_left_nonpos hyhi ahiNonpos
          exact ratLe_trans
            (ratLe_trans
              (min4_le_fourth
                (ratMul alo blo) (ratMul alo bhi)
                (ratMul ahi blo) (ratMul ahi bhi))
              cornerToHi)
            hiToX

theorem intervalMul_encloses {A B : QInterval} {x y : Rat} :
    InInterval x A -> InInterval y B ->
      InInterval (ratMul x y) (intervalMul A B) := by
  intro hx hy
  constructor
  · unfold intervalMul
    exact intervalMul_lower hx.left hx.right hy.left hy.right
  · unfold intervalMul
    exact intervalMul_upper hx.left hx.right hy.left hy.right

def hornerEvalFrom (acc : Rat) : List Rat -> Rat -> Rat
  | [], _x => acc
  | a :: rest, x => hornerEvalFrom (ratAdd (ratMul acc x) a) rest x

def hornerEval (coeffs : List Rat) (x : Rat) : Rat :=
  hornerEvalFrom ratZero coeffs x

def hornerIntervalFrom (acc : QInterval) :
    List Rat -> Rat -> Rat -> QInterval
  | [], _xlo, _xhi => acc
  | a :: rest, xlo, xhi =>
      hornerIntervalFrom
        (intervalAdd
          (intervalMul acc { lo := xlo, hi := xhi })
          (singletonInterval a))
        rest xlo xhi

def hornerInterval (coeffs : List Rat) (xlo xhi : Rat) : Rat × Rat :=
  let I := hornerIntervalFrom (singletonInterval ratZero) coeffs xlo xhi
  (I.lo, I.hi)

private theorem hornerIntervalFrom_encloses
    (coeffs : List Rat) (acc : QInterval)
    (xlo xhi x accValue : Rat)
    (hxlo : ratLe xlo x)
    (hxhi : ratLe x xhi)
    (hacc : InInterval accValue acc) :
    InInterval (hornerEvalFrom accValue coeffs x)
      (hornerIntervalFrom acc coeffs xlo xhi) := by
  induction coeffs generalizing acc accValue with
  | nil =>
      exact hacc
  | cons a rest ih =>
      unfold hornerEvalFrom hornerIntervalFrom
      let xInterval : QInterval := { lo := xlo, hi := xhi }
      let productInterval := intervalMul acc xInterval
      let nextInterval :=
        intervalAdd productInterval (singletonInterval a)
      have hxIn : InInterval x xInterval :=
        And.intro hxlo hxhi
      have productIn :
          InInterval (ratMul accValue x) productInterval :=
        intervalMul_encloses hacc hxIn
      have aIn : InInterval a (singletonInterval a) :=
        And.intro (ratLe_refl a) (ratLe_refl a)
      have nextIn :
          InInterval (ratAdd (ratMul accValue x) a) nextInterval :=
        intervalAdd_encloses productIn aIn
      exact ih nextInterval (ratAdd (ratMul accValue x) a) nextIn

theorem hornerInterval_encloses
    (coeffs : List Rat) (xlo xhi x : Rat)
    (hxlo : ratLe xlo x)
    (hxhi : ratLe x xhi) :
    let r := hornerInterval coeffs xlo xhi
    ratLe r.1 (hornerEval coeffs x) ∧
      ratLe (hornerEval coeffs x) r.2 := by
  unfold hornerInterval hornerEval
  exact hornerIntervalFrom_encloses coeffs
    (singletonInterval ratZero) xlo xhi x ratZero
    hxlo hxhi
    (And.intro (ratLe_refl ratZero) (ratLe_refl ratZero))

end BEDC.Derived.RHRoute.IntervalMatrixPSD
