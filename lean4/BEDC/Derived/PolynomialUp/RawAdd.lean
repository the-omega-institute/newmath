import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

private theorem PolynomialSingletonAddFold_cons_hsame {x : BHist} {xs ys : List BHist} :
    hsame (PolynomialSingletonAddFold xs) (PolynomialSingletonAddFold ys) ->
      hsame (PolynomialSingletonAddFold (x :: xs)) (PolynomialSingletonAddFold (x :: ys)) := by
  intro tailSame
  exact congrArg (fun u : BHist => append x u) tailSame

private theorem PolynomialSingletonRawAdd_zero_remainder_empty_addFold_empty {t : List BHist} :
    PolynomialZeroRemainder t ->
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd t [])) BHist.Empty := by
  intro zeroRemainder
  induction zeroRemainder with
  | nil =>
      unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonZero
      exact hsame_refl BHist.Empty
  | cons headEmpty _tailZero ih =>
      unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
      exact append_eq_empty_iff.mpr
        (And.intro
          (append_eq_empty_iff.mpr (And.intro headEmpty (hsame_refl BHist.Empty)))
          ih)

theorem PolynomialSingletonRawAdd_left_zero_tail_addFold_invariance {xs ys t : List BHist} :
    PolynomialZeroRemainder t ->
      hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd (xs ++ t) ys))
        (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) ∧
        Cont (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) BHist.Empty
          (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys)) := by
  intro zeroTail
  have zeroTailRawAdd :
      forall {t ys : List BHist}, PolynomialZeroRemainder t ->
        hsame (PolynomialSingletonAddFold (PolynomialSingletonRawAdd t ys))
          (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] ys)) := by
    intro t ys zeroRemainder
    induction zeroRemainder generalizing ys with
    | nil =>
        exact hsame_refl (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] ys))
    | cons headEmpty _tailZero ih =>
        cases ys with
        | nil =>
            exact hsame_trans
              (PolynomialSingletonRawAdd_zero_remainder_empty_addFold_empty
                (PolynomialZeroRemainder.cons headEmpty _tailZero))
              (hsame_symm (by
                unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonZero
                exact hsame_refl BHist.Empty))
        | cons y ys =>
            have tailSame := ih (ys := ys)
            cases headEmpty
            unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
            exact PolynomialSingletonAddFold_cons_hsame (x := append BHist.Empty y) tailSame
  induction xs generalizing ys with
  | nil =>
      exact And.intro (zeroTailRawAdd zeroTail)
        (cont_right_unit (PolynomialSingletonAddFold (PolynomialSingletonRawAdd [] ys)))
  | cons x xs ih =>
      cases ys with
      | nil =>
          have tailData := ih (ys := [])
          unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
          exact And.intro
            (congrArg (fun u : BHist => append (append x BHist.Empty) u) tailData.left)
            (cont_right_unit
              (PolynomialSingletonAdd (append x BHist.Empty)
                (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs []))))
      | cons y ys =>
          have tailData := ih (ys := ys)
          unfold PolynomialSingletonRawAdd PolynomialSingletonAddFold PolynomialSingletonAdd
          exact And.intro
            (congrArg (fun u : BHist => append (append x y) u) tailData.left)
            (cont_right_unit
              (PolynomialSingletonAdd (append x y)
                (PolynomialSingletonAddFold (PolynomialSingletonRawAdd xs ys))))

end BEDC.Derived.PolynomialUp
