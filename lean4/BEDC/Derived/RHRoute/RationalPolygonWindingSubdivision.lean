import BEDC.Derived.RHRoute.RationalPolygonWinding
import BEDC.Derived.RationalOrderArithUp
import BEDC.Derived.LocatedReal.GroundedToleranceKit
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 8000000

namespace BEDC.Derived.RHRoute.RationalPolygonWindingSubdivision

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.RationalPolygonWinding

abbrev Rat : Type :=
  BEDC.Derived.RationalUp.RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

def lerpPoint (a b : RatComplex) (t : Rat) : RatComplex :=
  { re := ratAdd a.re (ratMul t (ratSub b.re a.re))
    im := ratAdd a.im (ratMul t (ratSub b.im a.im)) }

private theorem ratSub_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro xx' yy'
  unfold ratSub
  exact ratAdd_respects xx' (ratNeg_respects yy')

private theorem ratMul_neg_right_local (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_sub_left_local (a b c : Rat) :
    RatEq (ratMul a (ratSub b c))
      (ratSub (ratMul a b) (ratMul a c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_left a b (ratNeg c))
    (ratAdd_respects (RatEq_refl (ratMul a b))
      (ratMul_neg_right_local a c))

private theorem ratMul_sub_right_local (a b c : Rat) :
    RatEq (ratMul (ratSub a b) c)
      (ratSub (ratMul a c) (ratMul b c)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratSub a b) c)
    (RatEq_trans _ _ _
      (ratMul_sub_left_local c a b)
      (ratSub_respects_local (ratMul_comm c a) (ratMul_comm c b)))

private theorem ratSub_common_left_local {x x' y z : Rat} :
    RatEq x x' ->
      RatEq (ratSub (ratAdd x y) (ratAdd x' z)) (ratSub y z) := by
  intro sameCommon
  unfold ratSub
  have negExpand :
      RatEq (ratAdd (ratAdd x y) (ratNeg (ratAdd x' z)))
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg z))) :=
    ratAdd_respects (RatEq_refl (ratAdd x y))
      (BEDC.Derived.LocatedReal.ratNeg_add_dist_local x' z)
  have commonAligned :
      RatEq (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg z)))
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x) (ratNeg z))) :=
    ratAdd_respects (RatEq_refl (ratAdd x y))
      (ratAdd_respects (ratNeg_respects (RatEq_symm sameCommon))
        (RatEq_refl (ratNeg z)))
  have paired :
      RatEq (ratAdd (ratAdd x y) (ratAdd (ratNeg x) (ratNeg z)))
        (ratAdd (ratAdd x (ratNeg x)) (ratAdd y (ratNeg z))) := by
    exact RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y
        (ratAdd (ratNeg x) (ratNeg z)))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x)
          (RatEq_symm
            (BEDC.Derived.LocatedReal.ratAdd_assoc_local
              y (ratNeg x) (ratNeg z))))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (ratAdd_respects (ratAdd_comm y (ratNeg x))
              (RatEq_refl (ratNeg z))))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl x)
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                (ratNeg x) y (ratNeg z)))
            (RatEq_symm
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                x (ratNeg x) (ratAdd y (ratNeg z)))))))
  exact RatEq_trans _ _ _ negExpand
    (RatEq_trans _ _ _ commonAligned
      (RatEq_trans _ _ _ paired
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local x)
            (RatEq_refl (ratAdd y (ratNeg z))))
          (ratZero_add_left (ratAdd y (ratNeg z))))))

private theorem ratSub_common_right_local {x z y y' : Rat} :
    RatEq y y' ->
      RatEq (ratSub (ratAdd x y) (ratAdd z y')) (ratSub x z) := by
  intro sameCommon
  exact RatEq_trans _ _ _
    (ratSub_respects_local (ratAdd_comm x y) (ratAdd_comm z y'))
    (ratSub_common_left_local sameCommon)

private theorem ratSub_sub_common_right_local (x y c : Rat) :
    RatEq (ratSub (ratSub x c) (ratSub y c)) (ratSub x y) := by
  change RatEq
    (ratSub (ratAdd x (ratNeg c)) (ratAdd y (ratNeg c)))
    (ratSub x y)
  exact ratSub_common_right_local (RatEq_refl (ratNeg c))

private theorem ratSub_sub_common_left_local (x y z : Rat) :
    RatEq (ratSub (ratSub x y) (ratSub x z)) (ratSub z y) := by
  change RatEq
    (ratSub (ratAdd x (ratNeg y)) (ratAdd x (ratNeg z)))
    (ratSub z y)
  exact RatEq_trans _ _ _
    (ratSub_common_left_local (RatEq_refl x))
    (RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratSub_neg_neg y z)
      (RatEq_symm (ratSub_swap_neg z y)))

private theorem ratSub_mul_left_factor_one_sub_local (t x : Rat) :
    RatEq (ratSub x (ratMul t x))
      (ratMul (ratSub ratOne t) x) := by
  exact RatEq_trans _ _ _
    (ratSub_respects_local (RatEq_symm (ratOne_mul_left x))
      (RatEq_refl (ratMul t x)))
    (RatEq_symm (ratMul_sub_right_local ratOne t x))

private theorem ratSub_factor_left_local (t x y : Rat) :
    RatEq (ratSub (ratMul t x) (ratMul t y))
      (ratMul t (ratSub x y)) :=
  RatEq_symm (ratMul_sub_left_local t x y)

private theorem ratMul_assoc_commute_middle_local (a t x : Rat) :
    RatEq (ratMul a (ratMul t x)) (ratMul t (ratMul a x)) := by
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc a t x))
    (RatEq_trans _ _ _
      (ratMul_respects (ratMul_comm a t) (RatEq_refl x))
      (ratMul_assoc t a x))

private theorem rayIntersectionNumerator_lerp_inner_local
    (ar ai br bi : Rat) :
    RatEq
      (ratSub (ratMul ar (ratSub bi ai))
        (ratMul (ratSub br ar) ai))
      (ratSub (ratMul ar bi) (ratMul br ai)) := by
  have leftExpand :
      RatEq (ratMul ar (ratSub bi ai))
        (ratSub (ratMul ar bi) (ratMul ar ai)) :=
    ratMul_sub_left_local ar bi ai
  have rightExpand :
      RatEq (ratMul (ratSub br ar) ai)
        (ratSub (ratMul br ai) (ratMul ar ai)) :=
    ratMul_sub_right_local br ar ai
  exact RatEq_trans _ _ _
    (ratSub_respects_local leftExpand rightExpand)
    (ratSub_sub_common_right_local
      (ratMul ar bi) (ratMul br ai) (ratMul ar ai))

private theorem rayIntersectionNumerator_lerp_target_inner_local
    (ar ai br bi : Rat) :
    RatEq
      (ratSub (ratMul (ratSub br ar) bi)
        (ratMul br (ratSub bi ai)))
      (ratSub (ratMul br ai) (ratMul ar bi)) := by
  have leftExpand :
      RatEq (ratMul (ratSub br ar) bi)
        (ratSub (ratMul br bi) (ratMul ar bi)) :=
    ratMul_sub_right_local br ar bi
  have rightExpand :
      RatEq (ratMul br (ratSub bi ai))
        (ratSub (ratMul br bi) (ratMul br ai)) :=
    ratMul_sub_left_local br bi ai
  exact RatEq_trans _ _ _
    (ratSub_respects_local leftExpand rightExpand)
    (ratSub_sub_common_left_local
      (ratMul br bi) (ratMul ar bi) (ratMul br ai))

theorem rayIntersectionNumerator_lerpPoint_source
    (a b : RatComplex) (t : Rat) :
    RatEq (rayIntersectionNumerator a (lerpPoint a b t))
      (ratMul t (rayIntersectionNumerator a b)) := by
  cases a with
  | mk ar ai =>
  cases b with
  | mk br bi =>
      unfold lerpPoint rayIntersectionNumerator
        BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub
      have leftExpand :
          RatEq
            (ratMul ar
              (ratAdd ai (ratMul t (ratSub bi ai))))
            (ratAdd (ratMul ar ai)
              (ratMul ar (ratMul t (ratSub bi ai)))) :=
        BEDC.Real.RatNumKernel.ratMul_add_left
          ar ai (ratMul t (ratSub bi ai))
      have rightExpand :
          RatEq
            (ratMul
              (ratAdd br (ratMul t (ratSub br br)))
              ai)
            (ratAdd (ratMul br ai)
              (ratMul (ratMul t (ratSub br br)) ai)) :=
        BEDC.Real.RatNumKernel.ratMul_add_right
          br (ratMul t (ratSub br br)) ai
      have rightExpandActual :
          RatEq
            (ratMul
              (ratAdd ar (ratMul t (ratSub br ar)))
              ai)
            (ratAdd (ratMul ar ai)
              (ratMul (ratMul t (ratSub br ar)) ai)) :=
        BEDC.Real.RatNumKernel.ratMul_add_right
          ar (ratMul t (ratSub br ar)) ai
      have toExpanded :
          RatEq
            (ratSub
              (ratMul ar
                (ratAdd ai (ratMul t (ratSub bi ai))))
              (ratMul
                (ratAdd ar (ratMul t (ratSub br ar)))
                ai))
            (ratSub
              (ratAdd (ratMul ar ai)
                (ratMul ar (ratMul t (ratSub bi ai))))
              (ratAdd (ratMul ar ai)
                (ratMul (ratMul t (ratSub br ar)) ai))) :=
        ratSub_respects_local leftExpand rightExpandActual
      have cancelCommon :
          RatEq
            (ratSub
              (ratAdd (ratMul ar ai)
                (ratMul ar (ratMul t (ratSub bi ai))))
              (ratAdd (ratMul ar ai)
                (ratMul (ratMul t (ratSub br ar)) ai)))
            (ratSub
              (ratMul ar (ratMul t (ratSub bi ai)))
              (ratMul (ratMul t (ratSub br ar)) ai)) :=
        ratSub_common_left_local (RatEq_refl (ratMul ar ai))
      have termLeft :
          RatEq
            (ratMul ar (ratMul t (ratSub bi ai)))
            (ratMul t (ratMul ar (ratSub bi ai))) :=
        ratMul_assoc_commute_middle_local ar t (ratSub bi ai)
      have termRight :
          RatEq
            (ratMul (ratMul t (ratSub br ar)) ai)
            (ratMul t (ratMul (ratSub br ar) ai)) :=
        ratMul_assoc t (ratSub br ar) ai
      have factorTerms :
          RatEq
            (ratSub
              (ratMul ar (ratMul t (ratSub bi ai)))
              (ratMul (ratMul t (ratSub br ar)) ai))
            (ratSub
              (ratMul t (ratMul ar (ratSub bi ai)))
              (ratMul t (ratMul (ratSub br ar) ai))) :=
        ratSub_respects_local termLeft termRight
      have factor :
          RatEq
            (ratSub
              (ratMul t (ratMul ar (ratSub bi ai)))
              (ratMul t (ratMul (ratSub br ar) ai)))
            (ratMul t
              (ratSub
                (ratMul ar (ratSub bi ai))
                (ratMul (ratSub br ar) ai))) :=
        ratSub_factor_left_local t
          (ratMul ar (ratSub bi ai))
          (ratMul (ratSub br ar) ai)
      have inner :
          RatEq
            (ratSub
              (ratMul ar (ratSub bi ai))
              (ratMul (ratSub br ar) ai))
            (ratSub (ratMul ar bi) (ratMul br ai)) :=
        rayIntersectionNumerator_lerp_inner_local ar ai br bi
      exact RatEq_trans _ _ _ toExpanded
        (RatEq_trans _ _ _ cancelCommon
          (RatEq_trans _ _ _ factorTerms
            (RatEq_trans _ _ _ factor
              (ratMul_respects (RatEq_refl t) inner))))

theorem rayIntersectionNumerator_lerpPoint_target
    (a b : RatComplex) (t : Rat) :
    RatEq (rayIntersectionNumerator (lerpPoint a b t) b)
      (ratMul (ratSub ratOne t) (rayIntersectionNumerator a b)) := by
  cases a with
  | mk ar ai =>
  cases b with
  | mk br bi =>
      unfold lerpPoint rayIntersectionNumerator
        BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub
      have leftExpand :
          RatEq
            (ratMul
              (ratAdd ar (ratMul t (ratSub br ar)))
              bi)
            (ratAdd (ratMul ar bi)
              (ratMul (ratMul t (ratSub br ar)) bi)) :=
        BEDC.Real.RatNumKernel.ratMul_add_right
          ar (ratMul t (ratSub br ar)) bi
      have rightExpand :
          RatEq
            (ratMul br
              (ratAdd ai (ratMul t (ratSub bi ai))))
            (ratAdd (ratMul br ai)
              (ratMul br (ratMul t (ratSub bi ai)))) :=
        BEDC.Real.RatNumKernel.ratMul_add_left
          br ai (ratMul t (ratSub bi ai))
      have toExpanded :
          RatEq
            (ratSub
              (ratMul
                (ratAdd ar (ratMul t (ratSub br ar)))
                bi)
              (ratMul br
                (ratAdd ai (ratMul t (ratSub bi ai)))))
            (ratSub
              (ratAdd (ratMul ar bi)
                (ratMul (ratMul t (ratSub br ar)) bi))
              (ratAdd (ratMul br ai)
                (ratMul br (ratMul t (ratSub bi ai))))) :=
        ratSub_respects_local leftExpand rightExpand
      have splitSums :
          RatEq
            (ratSub
              (ratAdd (ratMul ar bi)
                (ratMul (ratMul t (ratSub br ar)) bi))
              (ratAdd (ratMul br ai)
                (ratMul br (ratMul t (ratSub bi ai)))))
            (ratAdd
              (ratSub (ratMul ar bi) (ratMul br ai))
              (ratSub
                (ratMul (ratMul t (ratSub br ar)) bi)
                (ratMul br (ratMul t (ratSub bi ai))))) := by
        unfold ratSub
        have negExpand :
            RatEq
              (ratAdd
                (ratAdd (ratMul ar bi)
                  (ratMul (ratMul t (ratSub br ar)) bi))
                (ratNeg
                  (ratAdd (ratMul br ai)
                    (ratMul br (ratMul t (ratSub bi ai))))))
              (ratAdd
                (ratAdd (ratMul ar bi)
                  (ratMul (ratMul t (ratSub br ar)) bi))
                (ratAdd (ratNeg (ratMul br ai))
                  (ratNeg (ratMul br (ratMul t (ratSub bi ai)))))) :=
          ratAdd_respects (RatEq_refl _)
            (BEDC.Derived.LocatedReal.ratNeg_add_dist_local
              (ratMul br ai)
              (ratMul br (ratMul t (ratSub bi ai))))
        have paired :
            RatEq
              (ratAdd
                (ratAdd (ratMul ar bi)
                  (ratMul (ratMul t (ratSub br ar)) bi))
                (ratAdd (ratNeg (ratMul br ai))
                  (ratNeg (ratMul br (ratMul t (ratSub bi ai))))))
              (ratAdd
                (ratAdd (ratMul ar bi) (ratNeg (ratMul br ai)))
                (ratAdd
                  (ratMul (ratMul t (ratSub br ar)) bi)
                  (ratNeg (ratMul br (ratMul t (ratSub bi ai)))))) := by
          exact RatEq_trans _ _ _
            (BEDC.Derived.LocatedReal.ratAdd_assoc_local
              (ratMul ar bi)
              (ratMul (ratMul t (ratSub br ar)) bi)
              (ratAdd (ratNeg (ratMul br ai))
                (ratNeg (ratMul br (ratMul t (ratSub bi ai))))))
            (RatEq_trans _ _ _
              (ratAdd_respects (RatEq_refl (ratMul ar bi))
                (RatEq_symm
                  (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                    (ratMul (ratMul t (ratSub br ar)) bi)
                    (ratNeg (ratMul br ai))
                    (ratNeg (ratMul br
                      (ratMul t (ratSub bi ai)))))))
              (RatEq_trans _ _ _
                (ratAdd_respects (RatEq_refl (ratMul ar bi))
                  (ratAdd_respects
                    (ratAdd_comm
                      (ratMul (ratMul t (ratSub br ar)) bi)
                      (ratNeg (ratMul br ai)))
                    (RatEq_refl
                      (ratNeg (ratMul br
                        (ratMul t (ratSub bi ai)))))))
                (RatEq_trans _ _ _
                  (ratAdd_respects (RatEq_refl (ratMul ar bi))
                    (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                      (ratNeg (ratMul br ai))
                      (ratMul (ratMul t (ratSub br ar)) bi)
                      (ratNeg (ratMul br
                        (ratMul t (ratSub bi ai))))))
                  (RatEq_symm
                    (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                      (ratMul ar bi)
                      (ratNeg (ratMul br ai))
                      (ratAdd
                        (ratMul (ratMul t (ratSub br ar)) bi)
                        (ratNeg (ratMul br
                          (ratMul t (ratSub bi ai))))))))))
        exact RatEq_trans _ _ _ negExpand paired
      have termLeft :
          RatEq
            (ratMul (ratMul t (ratSub br ar)) bi)
            (ratMul t (ratMul (ratSub br ar) bi)) :=
        ratMul_assoc t (ratSub br ar) bi
      have termRight :
          RatEq
            (ratMul br (ratMul t (ratSub bi ai)))
            (ratMul t (ratMul br (ratSub bi ai))) :=
        ratMul_assoc_commute_middle_local br t (ratSub bi ai)
      have factorTerms :
          RatEq
            (ratSub
              (ratMul (ratMul t (ratSub br ar)) bi)
              (ratMul br (ratMul t (ratSub bi ai))))
            (ratSub
              (ratMul t (ratMul (ratSub br ar) bi))
              (ratMul t (ratMul br (ratSub bi ai)))) :=
        ratSub_respects_local termLeft termRight
      have factor :
          RatEq
            (ratSub
              (ratMul t (ratMul (ratSub br ar) bi))
              (ratMul t (ratMul br (ratSub bi ai))))
            (ratMul t
              (ratSub
                (ratMul (ratSub br ar) bi)
                (ratMul br (ratSub bi ai)))) :=
        ratSub_factor_left_local t
          (ratMul (ratSub br ar) bi)
          (ratMul br (ratSub bi ai))
      have inner :
          RatEq
            (ratSub
              (ratMul (ratSub br ar) bi)
              (ratMul br (ratSub bi ai)))
            (ratSub (ratMul br ai) (ratMul ar bi)) :=
        rayIntersectionNumerator_lerp_target_inner_local ar ai br bi
      have orient :
          RatEq (ratSub (ratMul br ai) (ratMul ar bi))
            (ratNeg (ratSub (ratMul ar bi) (ratMul br ai))) :=
        ratSub_swap_neg (ratMul br ai) (ratMul ar bi)
      have tNeg :
          RatEq
            (ratMul t (ratSub (ratMul br ai) (ratMul ar bi)))
            (ratNeg (ratMul t
              (ratSub (ratMul ar bi) (ratMul br ai)))) :=
        RatEq_trans _ _ _
          (ratMul_respects (RatEq_refl t) orient)
          (ratMul_neg_right_local t
            (ratSub (ratMul ar bi) (ratMul br ai)))
      have tailToNeg :
          RatEq
            (ratSub
              (ratMul (ratMul t (ratSub br ar)) bi)
              (ratMul br (ratMul t (ratSub bi ai))))
            (ratNeg (ratMul t
              (ratSub (ratMul ar bi) (ratMul br ai)))) :=
        RatEq_trans _ _ _ factorTerms
          (RatEq_trans _ _ _ factor
            (RatEq_trans _ _ _
              (ratMul_respects (RatEq_refl t) inner)
              tNeg))
      have toSub :
          RatEq
            (ratAdd
              (ratSub (ratMul ar bi) (ratMul br ai))
              (ratSub
                (ratMul (ratMul t (ratSub br ar)) bi)
                (ratMul br (ratMul t (ratSub bi ai)))))
            (ratSub
              (ratSub (ratMul ar bi) (ratMul br ai))
              (ratMul t
                (ratSub (ratMul ar bi) (ratMul br ai)))) :=
        ratAdd_respects
          (RatEq_refl (ratSub (ratMul ar bi) (ratMul br ai)))
          tailToNeg
      have oneSub :
          RatEq
            (ratSub
              (ratSub (ratMul ar bi) (ratMul br ai))
              (ratMul t
                (ratSub (ratMul ar bi) (ratMul br ai))))
            (ratMul (ratSub ratOne t)
              (ratSub (ratMul ar bi) (ratMul br ai))) :=
        ratSub_mul_left_factor_one_sub_local t
          (ratSub (ratMul ar bi) (ratMul br ai))
      exact RatEq_trans _ _ _ toExpanded
        (RatEq_trans _ _ _ splitSums
          (RatEq_trans _ _ _ toSub oneSub))

inductive allVerticesImPos : List RatComplex -> Prop where
  | nil : allVerticesImPos []
  | cons {v : RatComplex} {rest : List RatComplex} :
      ratLt ratZero v.im ->
        allVerticesImPos rest ->
          allVerticesImPos (v :: rest)

inductive allVerticesImNeg : List RatComplex -> Prop where
  | nil : allVerticesImNeg []
  | cons {v : RatComplex} {rest : List RatComplex} :
      ratLt v.im ratZero ->
        allVerticesImNeg rest ->
          allVerticesImNeg (v :: rest)

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem ratLtBool_false_of_not_ratLt {x y : Rat} :
    (ratLt x y -> False) -> ratLtBool x y = false := by
  intro notLt
  cases h : ratLtBool x y with
  | false => rfl
  | true => exact False.elim (notLt (ratLtBool_true_to_ratLt h))

private theorem ratLeBool_false_of_not_ratLe {x y : Rat} :
    (ratLe x y -> False) -> ratLeBool x y = false := by
  intro notLe
  cases h : ratLeBool x y with
  | false => rfl
  | true => exact False.elim (notLe (ratLeBool_true_to_ratLe h))

private theorem positive_not_nonpositive {q : Rat} :
    ratLt ratZero q -> ratLe q ratZero -> False := by
  intro pos nonpos
  exact ratLt_not_ratLe_reverse pos nonpos

private theorem negative_not_positive {q : Rat} :
    ratLt q ratZero -> ratLt ratZero q -> False := by
  intro neg pos
  exact ratLt_not_ratLe_reverse neg (ratLt_to_ratLe pos)

private theorem upwardPositiveRayCrossingBool_false_of_source_positive
    {source target : RatComplex}
    (source_pos : ratLt ratZero source.im) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool
  rw [ratLeBool_false_of_not_ratLe
    (positive_not_nonpositive source_pos)]
  rfl

private theorem downwardPositiveRayCrossingBool_false_of_target_positive
    {source target : RatComplex}
    (target_pos : ratLt ratZero target.im) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
  rw [ratLeBool_false_of_not_ratLe
    (positive_not_nonpositive target_pos)]
  rfl

private theorem upwardPositiveRayCrossingBool_false_of_target_negative
    {source target : RatComplex}
    (target_neg : ratLt target.im ratZero) :
    upwardPositiveRayCrossingBool source target = false := by
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool ratStrictPositiveBool
  cases ratLeBool source.im ratZero with
  | false =>
      rfl
  | true =>
      rw [ratLtBool_false_of_not_ratLt
        (negative_not_positive target_neg)]
      rfl

private theorem downwardPositiveRayCrossingBool_false_of_source_negative
    {source target : RatComplex}
    (source_neg : ratLt source.im ratZero) :
    downwardPositiveRayCrossingBool source target = false := by
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
    ratStrictPositiveBool
  cases ratLeBool target.im ratZero with
  | false =>
      rfl
  | true =>
      rw [ratLtBool_false_of_not_ratLt
        (negative_not_positive source_neg)]
      rfl

theorem edgeCrossing_zero_of_upperHalfplane
    {edge : OrientedSegment}
    (source_pos : ratLt ratZero edge.source.im)
    (target_pos : ratLt ratZero edge.target.im) :
    edgeCrossing edge = 0 := by
  unfold edgeCrossing
  rw [upwardPositiveRayCrossingBool_false_of_source_positive source_pos]
  rw [downwardPositiveRayCrossingBool_false_of_target_positive target_pos]
  rfl

private theorem edgeCrossing_pair_zero_of_upperHalfplane
    (source target : RatComplex)
    (source_pos : ratLt ratZero source.im)
    (target_pos : ratLt ratZero target.im) :
    edgeCrossing { source := source, target := target } = 0 := by
  exact edgeCrossing_zero_of_upperHalfplane
    (edge := { source := source, target := target })
    source_pos target_pos

theorem edgeCrossing_zero_of_lowerHalfplane
    {edge : OrientedSegment}
    (source_neg : ratLt edge.source.im ratZero)
    (target_neg : ratLt edge.target.im ratZero) :
    edgeCrossing edge = 0 := by
  unfold edgeCrossing
  rw [upwardPositiveRayCrossingBool_false_of_target_negative target_neg]
  rw [downwardPositiveRayCrossingBool_false_of_source_negative source_neg]
  rfl

private theorem edgeCrossing_pair_zero_of_lowerHalfplane
    (source target : RatComplex)
    (source_neg : ratLt source.im ratZero)
    (target_neg : ratLt target.im ratZero) :
    edgeCrossing { source := source, target := target } = 0 := by
  exact edgeCrossing_zero_of_lowerHalfplane
    (edge := { source := source, target := target })
    source_neg target_neg

private theorem sumClosedEdgesFrom_zero_of_all_im_pos :
    ∀ (first previous : RatComplex) (vertices : List RatComplex),
      ratLt ratZero first.im ->
        ratLt ratZero previous.im ->
          allVerticesImPos vertices ->
            sumEdgeCrossings (closedEdgesFrom first previous vertices) = 0
  | first, previous, [], first_pos, previous_pos, _all_pos => by
      show edgeCrossing { source := previous, target := first } + 0 = 0
      have hEdge :
          edgeCrossing { source := previous, target := first } = 0 :=
        edgeCrossing_pair_zero_of_upperHalfplane previous first
          previous_pos first_pos
      calc
        edgeCrossing { source := previous, target := first } + 0 =
            0 + 0 := congrArg (fun x : Int => x + 0) hEdge
        _ = 0 := rfl
  | first, previous, vertex :: rest, first_pos, previous_pos, all_pos => by
      cases all_pos with
      | cons vertex_pos rest_pos =>
      show
        edgeCrossing { source := previous, target := vertex } +
            sumEdgeCrossings (closedEdgesFrom first vertex rest) = 0
      have hEdge :
          edgeCrossing { source := previous, target := vertex } = 0 :=
        edgeCrossing_pair_zero_of_upperHalfplane previous vertex
          previous_pos vertex_pos
      have hRest :
          sumEdgeCrossings (closedEdgesFrom first vertex rest) = 0 :=
        sumClosedEdgesFrom_zero_of_all_im_pos first vertex rest
          first_pos vertex_pos rest_pos
      calc
        edgeCrossing { source := previous, target := vertex } +
            sumEdgeCrossings (closedEdgesFrom first vertex rest) =
          0 + 0 := by
            rw [hEdge, hRest]
        _ = 0 := rfl

private theorem sumClosedEdgesFrom_zero_of_all_im_neg :
    ∀ (first previous : RatComplex) (vertices : List RatComplex),
      ratLt first.im ratZero ->
        ratLt previous.im ratZero ->
          allVerticesImNeg vertices ->
            sumEdgeCrossings (closedEdgesFrom first previous vertices) = 0
  | first, previous, [], first_neg, previous_neg, _all_neg => by
      show edgeCrossing { source := previous, target := first } + 0 = 0
      have hEdge :
          edgeCrossing { source := previous, target := first } = 0 :=
        edgeCrossing_pair_zero_of_lowerHalfplane previous first
          previous_neg first_neg
      calc
        edgeCrossing { source := previous, target := first } + 0 =
            0 + 0 := congrArg (fun x : Int => x + 0) hEdge
        _ = 0 := rfl
  | first, previous, vertex :: rest, first_neg, previous_neg, all_neg => by
      cases all_neg with
      | cons vertex_neg rest_neg =>
      show
        edgeCrossing { source := previous, target := vertex } +
            sumEdgeCrossings (closedEdgesFrom first vertex rest) = 0
      have hEdge :
          edgeCrossing { source := previous, target := vertex } = 0 :=
        edgeCrossing_pair_zero_of_lowerHalfplane previous vertex
          previous_neg vertex_neg
      have hRest :
          sumEdgeCrossings (closedEdgesFrom first vertex rest) = 0 :=
        sumClosedEdgesFrom_zero_of_all_im_neg first vertex rest
          first_neg vertex_neg rest_neg
      calc
        edgeCrossing { source := previous, target := vertex } +
            sumEdgeCrossings (closedEdgesFrom first vertex rest) =
          0 + 0 := by
            rw [hEdge, hRest]
        _ = 0 := rfl

theorem computedWinding_zero_of_all_im_pos
    (polygon : RationalPolygon)
    (all_pos : allVerticesImPos polygon.vertices) :
    computedWinding polygon = 0 := by
  unfold computedWinding polygonEdges closedEdges
  cases polygon with
  | mk vertices =>
  cases vertices with
  | nil =>
      rfl
  | cons first rest =>
      cases all_pos with
      | cons first_pos rest_pos =>
      exact sumClosedEdgesFrom_zero_of_all_im_pos first first rest
        first_pos first_pos rest_pos

theorem computedWinding_zero_of_all_im_neg
    (polygon : RationalPolygon)
    (all_neg : allVerticesImNeg polygon.vertices) :
    computedWinding polygon = 0 := by
  unfold computedWinding polygonEdges closedEdges
  cases polygon with
  | mk vertices =>
  cases vertices with
  | nil =>
      rfl
  | cons first rest =>
      cases all_neg with
      | cons first_neg rest_neg =>
      exact sumClosedEdgesFrom_zero_of_all_im_neg first first rest
        first_neg first_neg rest_neg

end BEDC.Derived.RHRoute.RationalPolygonWindingSubdivision
