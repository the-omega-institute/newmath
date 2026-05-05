import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ListUp

theorem PolynomialSingletonRawAdd_structural_swap {xs ys : List BHist}
    (scalarComm : forall {a b : BHist},
      PolynomialSingletonClassifier (append a b) (append b a)) :
    BEDC.Derived.ListUp.ListClassifierSpec PolynomialSingletonClassifier
      (PolynomialSingletonRawAdd xs ys) (PolynomialSingletonRawAdd ys xs) := by
  induction xs generalizing ys with
  | nil =>
      induction ys with
      | nil =>
          unfold PolynomialSingletonRawAdd BEDC.Derived.ListUp.ListClassifierSpec
          constructor
      | cons y ys ih =>
          unfold PolynomialSingletonRawAdd BEDC.Derived.ListUp.ListClassifierSpec
          exact And.intro scalarComm ih
  | cons x xs ih =>
      cases ys with
      | nil =>
          unfold PolynomialSingletonRawAdd BEDC.Derived.ListUp.ListClassifierSpec
          exact And.intro scalarComm (ih (ys := []))
      | cons y ys =>
          unfold PolynomialSingletonRawAdd BEDC.Derived.ListUp.ListClassifierSpec
          exact And.intro scalarComm (ih (ys := ys))

end BEDC.Derived.PolynomialUp
