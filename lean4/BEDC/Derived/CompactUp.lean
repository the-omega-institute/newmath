import BEDC.FKernel.Unary
import BEDC.FKernel.Cont

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CompactWitnessCarrier (subset located finite intermediate compact : BHist) : Prop :=
  UnaryHistory subset ∧ UnaryHistory located ∧ UnaryHistory finite ∧
    Cont subset located intermediate ∧ Cont intermediate finite compact

theorem CompactWitnessCarrier_finite_extension_closed
    {subset located finite extra intermediate compact newFinite extended : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact -> UnaryHistory extra ->
      Cont finite extra newFinite -> Cont compact extra extended ->
        CompactWitnessCarrier subset located newFinite intermediate extended := by
  intro carrier extraCarrier finiteExtra compactExtra
  cases carrier with
  | intro subsetCarrier rest =>
      cases rest with
      | intro locatedCarrier rest =>
          cases rest with
          | intro finiteCarrier rest =>
              cases rest with
              | intro locatedLedger finiteLedger =>
                  have newFiniteCarrier : UnaryHistory newFinite :=
                    unary_cont_closed finiteCarrier extraCarrier finiteExtra
                  have associated := cont_assoc_left_exists finiteLedger compactExtra
                  cases associated with
                  | intro joined joinedData =>
                      cases joinedData with
                      | intro joinedLedger extendedLedger =>
                          have sameJoined : hsame newFinite joined :=
                            cont_deterministic finiteExtra joinedLedger
                          cases sameJoined
                          exact
                            And.intro subsetCarrier
                              (And.intro locatedCarrier
                                (And.intro newFiniteCarrier
                                  (And.intro locatedLedger extendedLedger)))

end BEDC.Derived.CompactUp
