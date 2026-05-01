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

def CompactNetWitness (center precision net : BHist) : Prop :=
  UnaryHistory center ∧ UnaryHistory precision ∧ UnaryHistory net ∧ Cont center precision net

theorem CompactNetWitness_prefix_closed {p center precision net : BHist} :
    UnaryHistory p -> CompactNetWitness center precision net ->
      CompactNetWitness (append p center) precision (append p net) := by
  intro prefixCarrier witness
  cases witness with
  | intro centerCarrier rest =>
      cases rest with
      | intro precisionCarrier rest =>
          cases rest with
          | intro netCarrier netRel =>
              cases netRel
              exact
                And.intro
                  (unary_append_closed prefixCarrier centerCarrier)
                  (And.intro precisionCarrier
                    (And.intro
                      (unary_append_closed prefixCarrier
                        (unary_cont_closed centerCarrier precisionCarrier (cont_intro rfl)))
                      (cont_intro (append_assoc p center precision).symm)))

end BEDC.Derived.CompactUp
