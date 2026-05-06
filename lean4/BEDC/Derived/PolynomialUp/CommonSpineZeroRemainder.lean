import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem PolynomialSingletonAddFold_common_spine_zero_remainder_hsame {p q r s : List BHist} :
    BEDC.Derived.ListUp.ListClassifierSpec hsame p q ->
      PolynomialZeroRemainder r -> PolynomialZeroRemainder s ->
        hsame (PolynomialSingletonAddFold (p ++ r)) (PolynomialSingletonAddFold (q ++ s)) ∧
          hsame (PolynomialSingletonAddFold (p ++ r))
            (append (PolynomialSingletonAddFold p) (PolynomialSingletonAddFold r)) := by
  intro spineSame zeroR zeroS
  have pRAppend :
      hsame (PolynomialSingletonAddFold (p ++ r))
        (append (PolynomialSingletonAddFold p) (PolynomialSingletonAddFold r)) :=
    PolynomialSingletonAddFold_append_hsame
  have qSAppend :
      hsame (PolynomialSingletonAddFold (q ++ s))
        (append (PolynomialSingletonAddFold q) (PolynomialSingletonAddFold s)) :=
    PolynomialSingletonAddFold_append_hsame
  have spineFoldSame :
      hsame (PolynomialSingletonAddFold p) (PolynomialSingletonAddFold q) :=
    (PolynomialSingletonAddFold_list_classifier_hsame spineSame).left
  have foldREmpty : hsame (PolynomialSingletonAddFold r) BHist.Empty :=
    PolynomialZeroRemainder_addFold_empty zeroR
  have foldSEmpty : hsame (PolynomialSingletonAddFold s) BHist.Empty :=
    PolynomialZeroRemainder_addFold_empty zeroS
  have pRToP :
      hsame (PolynomialSingletonAddFold (p ++ r)) (PolynomialSingletonAddFold p) :=
    hsame_trans pRAppend
      (hsame_trans (congrArg (append (PolynomialSingletonAddFold p)) foldREmpty)
        (append_empty_right (PolynomialSingletonAddFold p)))
  have qSToQ :
      hsame (PolynomialSingletonAddFold (q ++ s)) (PolynomialSingletonAddFold q) :=
    hsame_trans qSAppend
      (hsame_trans (congrArg (append (PolynomialSingletonAddFold q)) foldSEmpty)
        (append_empty_right (PolynomialSingletonAddFold q)))
  exact And.intro
    (hsame_trans pRToP (hsame_trans spineFoldSame (hsame_symm qSToQ)))
    pRAppend

end BEDC.Derived.PolynomialUp
