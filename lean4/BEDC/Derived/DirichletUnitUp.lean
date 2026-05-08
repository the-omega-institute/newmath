import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DirichletUnitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DirichletUnitHistoryCarrier
    (source unit inverse law unitLedger lawLedger provenance : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory unit ∧ UnaryHistory inverse ∧ UnaryHistory law ∧
    Cont source unit unitLedger ∧ Cont inverse law lawLedger ∧
      Cont unitLedger lawLedger provenance

theorem DirichletUnitHistoryCarrier_readback_obligation
    {source unit inverse law unitLedger lawLedger provenance : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      UnaryHistory unitLedger ∧ UnaryHistory lawLedger ∧ UnaryHistory provenance ∧
        Cont source unit unitLedger ∧ Cont inverse law lawLedger ∧
          Cont unitLedger lawLedger provenance := by
  intro carrier
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.right.left
  have lawLedgerUnary : UnaryHistory lawLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed unitLedgerUnary lawLedgerUnary carrier.right.right.right.right.right.right
  exact And.intro unitLedgerUnary
    (And.intro lawLedgerUnary
      (And.intro provenanceUnary
        (And.intro carrier.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.left
            carrier.right.right.right.right.right.right))))

theorem DirichletUnitHistoryCarrier_visible_unit_rows
    {source unit inverse law unitLedger lawLedger provenance : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      UnaryHistory unit ∧ UnaryHistory inverse ∧ UnaryHistory unitLedger ∧
        UnaryHistory lawLedger ∧ UnaryHistory provenance ∧ Cont source unit unitLedger ∧
          Cont inverse law lawLedger ∧ Cont unitLedger lawLedger provenance := by
  intro carrier
  have readback :=
    DirichletUnitHistoryCarrier_readback_obligation
      (source := source) (unit := unit) (inverse := inverse) (law := law)
      (unitLedger := unitLedger) (lawLedger := lawLedger) (provenance := provenance) carrier
  exact And.intro carrier.right.left
    (And.intro carrier.right.right.left
      (And.intro readback.left
        (And.intro readback.right.left
          (And.intro readback.right.right.left
            (And.intro readback.right.right.right.left
              (And.intro readback.right.right.right.right.left
                readback.right.right.right.right.right))))))

theorem DirichletUnitHistoryCarrier_classifier_transport
    {source source' unit unit' inverse inverse' law law' unitLedger unitLedger'
      lawLedger lawLedger' provenance provenance' : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      hsame source source' -> hsame unit unit' -> hsame inverse inverse' ->
        hsame law law' -> Cont source' unit' unitLedger' ->
          Cont inverse' law' lawLedger' -> Cont unitLedger' lawLedger' provenance' ->
            DirichletUnitHistoryCarrier source' unit' inverse' law' unitLedger' lawLedger'
              provenance' ∧ hsame unitLedger unitLedger' ∧ hsame lawLedger lawLedger' ∧
                hsame provenance provenance' := by
  intro carrier sameSource sameUnit sameInverse sameLaw targetUnitCont targetLawCont
    targetProvenanceCont
  have sourceUnary : UnaryHistory source' :=
    unary_transport carrier.left sameSource
  have unitUnary : UnaryHistory unit' :=
    unary_transport carrier.right.left sameUnit
  have inverseUnary : UnaryHistory inverse' :=
    unary_transport carrier.right.right.left sameInverse
  have lawUnary : UnaryHistory law' :=
    unary_transport carrier.right.right.right.left sameLaw
  have sameUnitLedger : hsame unitLedger unitLedger' :=
    cont_respects_hsame sameSource sameUnit carrier.right.right.right.right.left targetUnitCont
  have sameLawLedger : hsame lawLedger lawLedger' :=
    cont_respects_hsame sameInverse sameLaw carrier.right.right.right.right.right.left
      targetLawCont
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameUnitLedger sameLawLedger carrier.right.right.right.right.right.right
      targetProvenanceCont
  exact And.intro
    (And.intro sourceUnary
      (And.intro unitUnary
        (And.intro inverseUnary
          (And.intro lawUnary
            (And.intro targetUnitCont
              (And.intro targetLawCont targetProvenanceCont))))))
    (And.intro sameUnitLedger (And.intro sameLawLedger sameProvenance))

end BEDC.Derived.DirichletUnitUp
