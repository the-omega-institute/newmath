import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_export_scope [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance nameCert exportRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory target →
      UnaryHistory active →
        UnaryHistory retired →
          UnaryHistory blocking →
            UnaryHistory exportRow →
              UnaryHistory transport →
                UnaryHistory replay →
                  Cont target active blocking →
                    Cont blocking exportRow exportRead →
                      Cont exportRead replay provenance →
                        PkgSig bundle provenance pkg →
                          hsame provenance publicRead →
                            hsame publicRead nameCert →
                              activeReadingGateFields
                                  (ActiveReadingGateUp.mk target active retired blocking
                                    exportRow transport replay provenance nameCert) =
                                [target, active, retired, blocking, exportRow, transport,
                                  replay, provenance, nameCert] ∧
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row target ∨ hsame row active ∨
                                        hsame row blocking ∨ hsame row exportRow ∨
                                          hsame row exportRead ∨ hsame row provenance ∨
                                            hsame row nameCert)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont target active blocking ∧
                                        Cont blocking exportRow exportRead ∧
                                          Cont exportRead replay provenance ∧
                                            PkgSig bundle provenance pkg)
                                    hsame ∧
                                  UnaryHistory exportRead ∧ UnaryHistory publicRead ∧
                                    UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _unaryTarget _unaryActive _unaryRetired unaryBlocking unaryExport _unaryTransport
    unaryReplay targetActive blockingExport exportReplay provenancePkg provenancePublic
    publicName
  have unaryExportRead : UnaryHistory exportRead :=
    unary_cont_closed unaryBlocking unaryExport blockingExport
  have unaryProvenance : UnaryHistory provenance :=
    unary_cont_closed unaryExportRead unaryReplay exportReplay
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_transport unaryProvenance provenancePublic
  have unaryNameCert : UnaryHistory nameCert :=
    unary_transport unaryPublicRead publicName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row active ∨ hsame row blocking ∨ hsame row exportRow ∨
              hsame row exportRead ∨ hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target active blocking ∧
              Cont blocking exportRow exportRead ∧ Cont exportRead replay provenance ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublicRead⟩
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
      have rowNameCert : hsame _ nameCert :=
        hsame_trans source.left publicName
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr rowNameCert)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, targetActive, blockingExport, exportReplay, provenancePkg⟩
  }
  exact ⟨rfl, cert, unaryExportRead, unaryPublicRead, unaryNameCert⟩

end BEDC.Derived.ActiveReadingGateUp
