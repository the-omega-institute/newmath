import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DirichletUnitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DirichletUnitHistoryCarrier_namecert_obligation_surface
    {source unit inverse law unitLedger lawLedger provenance : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      SemanticNameCert
          (fun h : BHist =>
            DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h)
          (fun h : BHist =>
            DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h)
          (fun h : BHist =>
            DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h)
          (fun h k : BHist =>
            hsame h k ∧
              DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h ∧
                DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger k) ∧
        Cont source unit unitLedger ∧ Cont inverse law lawLedger ∧
          Cont unitLedger lawLedger provenance := by
  intro carrier
  have cert :
      SemanticNameCert
          (fun h : BHist =>
            DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h)
          (fun h : BHist =>
            DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h)
          (fun h : BHist =>
            DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h)
          (fun h k : BHist =>
            hsame h k ∧
              DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger h ∧
                DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger k) := {
    core := {
      carrier_inhabited := Exists.intro provenance carrier
      equiv_refl := by
        intro h source
        exact And.intro (hsame_refl h) (And.intro source source)
      equiv_symm := by
        intro h k related
        exact And.intro (hsame_symm related.left)
          (And.intro related.right.right related.right.left)
      equiv_trans := by
        intro h k r relatedHK relatedKR
        exact And.intro (hsame_trans relatedHK.left relatedKR.left)
          (And.intro relatedHK.right.left relatedKR.right.right)
      carrier_respects_equiv := by
        intro h k related _source
        exact related.right.right
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact And.intro cert
    (And.intro carrier.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.left
        carrier.right.right.right.right.right.right))

theorem DirichletUnitHistoryCarrier_free_rank_witness_ledger
    {source unit inverse law unitLedger lawLedger provenance rankWitness rankLedger : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      UnaryHistory rankWitness ->
        Cont provenance rankWitness rankLedger ->
          UnaryHistory provenance ∧ UnaryHistory rankLedger ∧
            hsame rankLedger (append provenance rankWitness) ∧
              Cont unitLedger lawLedger provenance := by
  intro carrier rankWitnessUnary rankLedgerRow
  have readback :=
    DirichletUnitHistoryCarrier_readback_obligation
      (source := source) (unit := unit) (inverse := inverse) (law := law)
      (unitLedger := unitLedger) (lawLedger := lawLedger) (provenance := provenance) carrier
  have rankLedgerUnary : UnaryHistory rankLedger :=
    unary_cont_closed readback.right.right.left rankWitnessUnary rankLedgerRow
  exact And.intro readback.right.right.left
    (And.intro rankLedgerUnary
      (And.intro rankLedgerRow readback.right.right.right.right.right))

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

theorem DirichletUnitHistoryCarrier_abgroup_dependency_obligation
    {source unit inverse law unitLedger lawLedger provenance lawConsumer lawReadback : BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      UnaryHistory lawConsumer ->
        Cont law lawConsumer lawReadback ->
          UnaryHistory lawReadback ∧ hsame lawReadback (append law lawConsumer) ∧
            UnaryHistory law ∧ Cont inverse law lawLedger ∧
              Cont unitLedger lawLedger provenance := by
  intro carrier consumerUnary readbackRow
  have lawUnary : UnaryHistory law :=
    carrier.right.right.right.left
  have readbackUnary : UnaryHistory lawReadback :=
    unary_cont_closed lawUnary consumerUnary readbackRow
  exact And.intro readbackUnary
    (And.intro readbackRow
      (And.intro lawUnary
        (And.intro carrier.right.right.right.right.right.left
          carrier.right.right.right.right.right.right)))

theorem DirichletUnitHistoryCarrier_regulator_unit_row_source_exhaustion
    {source unit inverse law unitLedger lawLedger provenance regulatorRead unitRead inverseRead :
      BHist} :
    DirichletUnitHistoryCarrier source unit inverse law unitLedger lawLedger provenance ->
      Cont unit provenance unitRead ->
        Cont inverse provenance inverseRead ->
          Cont unitRead inverseRead regulatorRead ->
            UnaryHistory unit ∧ UnaryHistory inverse ∧ UnaryHistory unitRead ∧
              UnaryHistory inverseRead ∧ UnaryHistory regulatorRead ∧
                hsame unitRead (append unit provenance) ∧
                  hsame inverseRead (append inverse provenance) ∧
                    hsame regulatorRead (append unitRead inverseRead) ∧
                      Cont source unit unitLedger ∧ Cont unitLedger lawLedger provenance := by
  intro carrier unitRow inverseRow regulatorRow
  have readback :=
    DirichletUnitHistoryCarrier_readback_obligation
      (source := source) (unit := unit) (inverse := inverse) (law := law)
      (unitLedger := unitLedger) (lawLedger := lawLedger) (provenance := provenance) carrier
  have unitReadUnary : UnaryHistory unitRead :=
    unary_cont_closed carrier.right.left readback.right.right.left unitRow
  have inverseReadUnary : UnaryHistory inverseRead :=
    unary_cont_closed carrier.right.right.left readback.right.right.left inverseRow
  have regulatorReadUnary : UnaryHistory regulatorRead :=
    unary_cont_closed unitReadUnary inverseReadUnary regulatorRow
  exact And.intro carrier.right.left
    (And.intro carrier.right.right.left
      (And.intro unitReadUnary
        (And.intro inverseReadUnary
          (And.intro regulatorReadUnary
            (And.intro unitRow
              (And.intro inverseRow
                (And.intro regulatorRow
                  (And.intro carrier.right.right.right.right.left
                    readback.right.right.right.right.right))))))))

end BEDC.Derived.DirichletUnitUp
