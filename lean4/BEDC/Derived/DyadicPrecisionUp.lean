import BEDC.Derived.DyadicPrecisionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicPrecisionSchedule
    (precision radius window transport provenance nameCert ledger : BHist) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory radius ∧
      UnaryHistory window ∧
        UnaryHistory nameCert ∧
          Cont radius nameCert provenance ∧
            Cont precision window transport ∧
              Cont transport provenance ledger

theorem DyadicPrecisionSchedule_common_window_readback
    {precision radius window transport provenance nameCert ledger precision' radius' window'
      transport' provenance' nameCert' ledger' : BHist} :
    DyadicPrecisionSchedule precision radius window transport provenance nameCert ledger →
      DyadicPrecisionSchedule precision' radius' window' transport' provenance' nameCert'
        ledger' →
        hsame precision precision' →
          hsame window window' →
            hsame provenance provenance' →
              Cont precision' window' transport' →
                Cont transport' provenance' ledger' →
                  hsame transport transport' ∧ hsame ledger ledger' := by
  intro left _right samePrecision sameWindow sameProvenance rightTransport rightLedger
  have leftTransport : Cont precision window transport :=
    left.right.right.right.right.right.left
  have leftLedger : Cont transport provenance ledger :=
    left.right.right.right.right.right.right
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameWindow leftTransport rightTransport
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTransport sameProvenance leftLedger rightLedger
  exact And.intro sameTransport sameLedger

theorem DyadicPrecisionSchedule_radius_window_coverage
    {precision radius window transport provenance nameCert ledger : BHist} :
    DyadicPrecisionSchedule precision radius window transport provenance nameCert ledger ->
      UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory window ∧
        UnaryHistory nameCert ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
          UnaryHistory ledger ∧ hsame transport (append precision window) ∧
            hsame provenance (append radius nameCert) ∧
              hsame ledger (append transport provenance) := by
  intro schedule
  have precisionUnary : UnaryHistory precision :=
    schedule.left
  have radiusUnary : UnaryHistory radius :=
    schedule.right.left
  have windowUnary : UnaryHistory window :=
    schedule.right.right.left
  have nameCertUnary : UnaryHistory nameCert :=
    schedule.right.right.right.left
  have provenanceRow : Cont radius nameCert provenance :=
    schedule.right.right.right.right.left
  have transportRow : Cont precision window transport :=
    schedule.right.right.right.right.right.left
  have ledgerRow : Cont transport provenance ledger :=
    schedule.right.right.right.right.right.right
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed precisionUnary windowUnary transportRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed radiusUnary nameCertUnary provenanceRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed transportUnary provenanceUnary ledgerRow
  exact
    ⟨precisionUnary, radiusUnary, windowUnary, nameCertUnary, transportUnary,
      provenanceUnary, ledgerUnary, transportRow, provenanceRow, ledgerRow⟩

theorem DyadicPrecisionUp_semantic_name_certificate (x : DyadicPrecisionUp) :
    SemanticNameCert
      (fun row : BHist =>
        match x with
        | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
            hsame row precision ∨ hsame row radius ∨ hsame row window ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row nameCert ∨
                hsame row ledger)
      (fun row : BHist =>
        match x with
        | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
            hsame row precision ∨ hsame row radius ∨ hsame row window ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row nameCert ∨
                hsame row ledger)
      (fun row : BHist =>
        match x with
        | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
            hsame row precision ∨ hsame row radius ∨ hsame row window ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row nameCert ∨
                hsame row ledger)
      hsame := by
  cases x with
  | mk precision radius window transport provenance nameCert ledger =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro precision (Or.inl (hsame_refl precision))
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row row' sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro row row' row'' sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row row' sameRows source
            cases source with
            | inl samePrecision =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) samePrecision)
            | inr source =>
                cases source with
                | inl sameRadius =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRadius))
                | inr source =>
                    cases source with
                    | inl sameWindow =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)))
                    | inr source =>
                        cases source with
                        | inl sameTransport =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameTransport))))
                        | inr source =>
                            cases source with
                            | inl sameProvenance =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans
                                            (hsame_symm sameRows) sameProvenance)))))
                            | inr source =>
                                cases source with
                                | inl sameNameCert =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans
                                                  (hsame_symm sameRows) sameNameCert))))))
                                | inr sameLedger =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (hsame_trans
                                                  (hsame_symm sameRows) sameLedger))))))
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

def DyadicPrecisionEmptySchedule [AskSetup] [PackageSetup]
    (radius transport provenance nameRow ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory radius ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
    UnaryHistory nameRow ∧ UnaryHistory ledger ∧ Cont BHist.Empty radius BHist.Empty ∧
      Cont BHist.Empty transport provenance ∧ PkgSig bundle provenance pkg

theorem DyadicPrecisionEmptySchedule_exactness [AskSetup] [PackageSetup]
    {radius transport provenance nameRow ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger bundle pkg ->
      UnaryHistory BHist.Empty ∧ UnaryHistory radius ∧ UnaryHistory transport ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory ledger ∧
          Cont BHist.Empty radius BHist.Empty ∧ Cont BHist.Empty transport provenance ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert
                (fun row : BHist =>
                  DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
                    bundle pkg ∧ hsame row nameRow)
                (fun row : BHist =>
                  DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
                    bundle pkg ∧ hsame row nameRow)
                (fun row : BHist =>
                  DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
                    bundle pkg ∧ hsame row nameRow)
                hsame := by
  intro schedule
  have schedulePacket := schedule
  obtain ⟨radiusUnary, transportUnary, provenanceUnary, nameUnary, ledgerUnary,
    radiusRow, provenanceRow, pkgRow⟩ := schedule
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
            bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
            bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
            bundle pkg ∧ hsame row nameRow)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro schedulePacket (hsame_refl nameRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨unary_empty, radiusUnary, transportUnary, provenanceUnary, nameUnary, ledgerUnary,
      radiusRow, provenanceRow, pkgRow, semantic⟩

theorem DyadicPrecisionSchedule_successor_schedule_exactness
    {precision radius window transport provenance nameCert ledger successorPrecision
      successorTransport successorLedger : BHist} :
    DyadicPrecisionSchedule precision radius window transport provenance nameCert ledger ->
      Cont precision (BHist.e1 BHist.Empty) successorPrecision ->
        Cont successorPrecision window successorTransport ->
          Cont successorTransport provenance successorLedger ->
            UnaryHistory successorPrecision ∧ UnaryHistory successorTransport ∧
              UnaryHistory successorLedger ∧
                hsame successorPrecision (append precision (BHist.e1 BHist.Empty)) ∧
                  hsame successorTransport (append successorPrecision window) ∧
                    hsame successorLedger (append successorTransport provenance) := by
  intro schedule successorPrecisionRow successorTransportRow successorLedgerRow
  have precisionUnary : UnaryHistory precision :=
    schedule.left
  have windowUnary : UnaryHistory window :=
    schedule.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed schedule.right.left schedule.right.right.right.left
      schedule.right.right.right.right.left
  have successorBaseUnary : UnaryHistory (BHist.e1 BHist.Empty) :=
    unary_e1_closed unary_empty
  have successorPrecisionUnary : UnaryHistory successorPrecision :=
    unary_cont_closed precisionUnary successorBaseUnary successorPrecisionRow
  have successorTransportUnary : UnaryHistory successorTransport :=
    unary_cont_closed successorPrecisionUnary windowUnary successorTransportRow
  have successorLedgerUnary : UnaryHistory successorLedger :=
    unary_cont_closed successorTransportUnary provenanceUnary successorLedgerRow
  exact
    ⟨successorPrecisionUnary, successorTransportUnary, successorLedgerUnary,
      successorPrecisionRow, successorTransportRow, successorLedgerRow⟩

end BEDC.Derived.DyadicPrecisionUp
