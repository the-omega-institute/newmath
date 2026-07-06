import BEDC.Derived.ActiveReadingGateUp.LedgerNonescape
import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def ActiveReadingGateCarrier_current_retired_boundary_carrier [AskSetup] [PackageSetup]
    (target active retired blocking exportRow transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: ActiveReadingGateUp BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  FieldFaithful.fields
      (ActiveReadingGateUp.mk target active retired blocking exportRow transport replay
        provenance localName) =
    [target, active, retired, blocking, exportRow, transport, replay, provenance,
      localName] ∧
    UnaryHistory retired ∧ UnaryHistory active ∧ UnaryHistory exportRow ∧
      Cont active blocking exportRow ∧ Cont retired transport replay ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem ActiveReadingGateCarrier_current_retired_disjointness [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert activeExport
      retiredAudit publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target ->
      UnaryHistory active ->
        UnaryHistory retired ->
          UnaryHistory blocking ->
            UnaryHistory exportRow ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont target active blocking ->
                    Cont blocking exportRow activeExport ->
                      Cont retired transport retiredAudit ->
                        Cont activeExport replay provenance ->
                          PkgSig bundle provenance pkg ->
                            hsame provenance publicRead ->
                              hsame publicRead nameCert ->
                                activeReadingGateFields
                                    (ActiveReadingGateUp.mk target active retired blocking
                                      exportRow transport replay provenance nameCert) =
                                  [target, active, retired, blocking, exportRow, transport,
                                    replay, provenance, nameCert] ∧
                                  SemanticNameCert
                                      (fun row : BHist => hsame row activeExport ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row target ∨ hsame row active ∨
                                          hsame row retired ∨ hsame row blocking ∨
                                            hsame row exportRow ∨ hsame row activeExport ∨
                                              hsame row retiredAudit ∨ hsame row provenance ∨
                                                hsame row nameCert)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont target active blocking ∧
                                          Cont blocking exportRow activeExport ∧
                                            Cont retired transport retiredAudit ∧
                                              Cont activeExport replay provenance ∧
                                                PkgSig bundle provenance pkg)
                                      hsame ∧
                                    UnaryHistory activeExport ∧ UnaryHistory retiredAudit ∧
                                      UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro _targetUnary activeUnary retiredUnary blockingUnary exportUnary transportUnary replayUnary
    targetActive blockingExport retiredTransport exportReplay provenancePkg provenancePublic
    publicName
  have activeExportUnary : UnaryHistory activeExport :=
    unary_cont_closed blockingUnary exportUnary blockingExport
  have retiredAuditUnary : UnaryHistory retiredAudit :=
    unary_cont_closed retiredUnary transportUnary retiredTransport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed activeExportUnary replayUnary exportReplay
  have nameCertUnary : UnaryHistory nameCert :=
    unary_transport (unary_transport provenanceUnary provenancePublic) publicName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row activeExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row retired ∨ hsame row blocking ∨
              hsame row exportRow ∨ hsame row activeExport ∨ hsame row retiredAudit ∨
                hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target active blocking ∧
              Cont blocking exportRow activeExport ∧ Cont retired transport retiredAudit ∧
                Cont activeExport replay provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro activeExport ⟨hsame_refl activeExport, activeExportUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, targetActive, blockingExport, retiredTransport, exportReplay,
          provenancePkg⟩
  }
  exact ⟨rfl, cert, activeExportUnary, retiredAuditUnary, nameCertUnary⟩

theorem ActiveReadingGateCarrier_current_retired_boundary [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ActiveReadingGateCarrier_current_retired_boundary_carrier target active retired blocking
        exportRow transport replay provenance localName bundle pkg →
      UnaryHistory retired ∧ UnaryHistory active ∧ UnaryHistory exportRow ∧
        Cont active blocking exportRow ∧ Cont retired transport replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: ActiveReadingGateUp BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  obtain ⟨fieldRows, retiredUnary, activeUnary, exportUnary, activeBlockingExport,
    retiredTransportReplay, provenancePkg, localNamePkg⟩ := carrier
  cases fieldRows
  exact
    ⟨retiredUnary, activeUnary, exportUnary, activeBlockingExport, retiredTransportReplay,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.ActiveReadingGateUp
