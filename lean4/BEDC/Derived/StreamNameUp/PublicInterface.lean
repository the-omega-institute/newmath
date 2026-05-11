import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamNameFiniteWindowClassifier_public_interface
    {s t u s' t' : BHist -> BHist} {bundle : ProbeBundle BHist} :
    (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> RatHistoryCarrier (s n)) ->
      RatStreamNameFiniteWindowClassifier s t bundle ->
        RatStreamNameFiniteWindowClassifier t u bundle ->
          (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> hsame (s n) (s' n)) ->
            (forall {n : BHist}, InBundle n bundle -> UnaryHistory n -> hsame (t n) (t' n)) ->
              RatStreamNameFiniteWindowClassifier s s bundle ∧
                RatStreamNameFiniteWindowClassifier t s bundle ∧
                  RatStreamNameFiniteWindowClassifier s u bundle ∧
                    RatStreamNameFiniteWindowClassifier s' t' bundle ∧
                      (forall {n : BHist}, InBundle n bundle -> UnaryHistory n ->
                        PositiveUnaryDenominator (s n) ∧
                          PositiveUnaryDenominator (t n)) := by
  intro carrierS classifiedST classifiedTU sameSS' sameTT'
  have stability :=
    RatStreamNameFiniteWindowClassifier_stability_fields carrierS classifiedST classifiedTU
      sameSS' sameTT'
  have positiveRows :
      forall {n : BHist}, InBundle n bundle -> UnaryHistory n ->
        PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) := by
    intro n member nUnary
    exact RatHistoryClassifier_positive_denominators (classifiedST n member nUnary)
  exact And.intro stability.left
    (And.intro stability.right.left
      (And.intro stability.right.right.left
        (And.intro stability.right.right.right positiveRows)))

theorem RatStreamNameFiniteWindowClassifier_public_ledger_obligation
    {s t : BHist -> BHist} {bundle selected : ProbeBundle BHist} :
    (forall {n : BHist}, InBundle n selected -> InBundle n bundle) ->
      RatStreamNameFiniteWindowClassifier s t bundle ->
        (forall {n : BHist}, InBundle n selected -> UnaryHistory n -> RatHistoryCarrier (s n)) ->
          RatStreamNameFiniteWindowClassifier s t selected ∧
            (forall {n : BHist}, InBundle n selected -> UnaryHistory n ->
              RatHistoryClassifier (s n) (t n) ∧ PositiveUnaryDenominator (s n) ∧
                PositiveUnaryDenominator (t n)) := by
  intro selectedInBundle classified carrierSelected
  have selectedClassifier : RatStreamNameFiniteWindowClassifier s t selected := by
    intro n selectedMember nUnary
    exact classified n (selectedInBundle selectedMember) nUnary
  have ledgerRows :
      forall {n : BHist}, InBundle n selected -> UnaryHistory n ->
        RatHistoryClassifier (s n) (t n) ∧ PositiveUnaryDenominator (s n) ∧
          PositiveUnaryDenominator (t n) := by
    intro n selectedMember nUnary
    have classifiedPoint : RatHistoryClassifier (s n) (t n) :=
      classified n (selectedInBundle selectedMember) nUnary
    have denominatorS : PositiveUnaryDenominator (s n) :=
      RatHistoryCarrier_iff_positive_denominator.mp (carrierSelected selectedMember nUnary)
    have denominatorT : PositiveUnaryDenominator (t n) :=
      (RatHistoryClassifier_positive_denominators classifiedPoint).right
    exact ⟨classifiedPoint, denominatorS, denominatorT⟩
  exact And.intro selectedClassifier ledgerRows

end BEDC.Derived.StreamNameUp
