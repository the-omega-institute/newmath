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

theorem CompactWitnessCarrier_located_extension_closed
    {subset located finite extra intermediate compact newLocated newIntermediate extended : BHist} :
    CompactWitnessCarrier subset located finite intermediate compact -> UnaryHistory extra ->
      Cont located extra newLocated -> Cont intermediate extra newIntermediate ->
        Cont newIntermediate finite extended ->
          CompactWitnessCarrier subset newLocated finite newIntermediate extended := by
  intro carrier extraCarrier locatedExtra intermediateExtra extendedLedger
  cases carrier with
  | intro subsetCarrier rest =>
      cases rest with
      | intro locatedCarrier rest =>
          cases rest with
          | intro finiteCarrier rest =>
              cases rest with
              | intro locatedLedger _compactLedger =>
                  have newLocatedCarrier : UnaryHistory newLocated :=
                    unary_cont_closed locatedCarrier extraCarrier locatedExtra
                  have associated := cont_assoc_left_exists locatedLedger intermediateExtra
                  cases associated with
                  | intro shifted shiftedData =>
                      cases shiftedData with
                      | intro shiftedLocated subsetShifted =>
                          have sameShifted : hsame newLocated shifted :=
                            cont_deterministic locatedExtra shiftedLocated
                          cases sameShifted
                          exact
                            And.intro subsetCarrier
                              (And.intro newLocatedCarrier
                                (And.intro finiteCarrier
                                  (And.intro subsetShifted extendedLedger)))

theorem CompactNetWitness_prefix_iff {p center precision net : BHist} :
    CompactNetWitness (append p center) precision (append p net) ↔
      UnaryHistory p ∧ CompactNetWitness center precision net := by
  constructor
  · intro witness
    cases witness with
    | intro prefixedCenter rest =>
        cases rest with
        | intro precisionCarrier rest =>
            cases rest with
            | intro prefixedNet netRel =>
                exact
                  And.intro (unary_append_left_factor prefixedCenter)
                    (And.intro (unary_append_right_factor prefixedCenter)
                      (And.intro precisionCarrier
                        (And.intro (unary_append_right_factor prefixedNet)
                          (cont_prefix_cancel netRel))))
  · intro prefixed
    cases prefixed with
    | intro prefixCarrier witness =>
        exact CompactNetWitness_prefix_closed prefixCarrier witness

end BEDC.Derived.CompactUp
