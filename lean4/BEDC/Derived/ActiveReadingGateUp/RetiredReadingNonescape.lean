import BEDC.Derived.ActiveReadingGateUp.TasteGate

namespace BEDC.Derived.ActiveReadingGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ActiveReadingGateCarrier_retired_reading_nonescape [AskSetup] [PackageSetup]
    {target active retired blocking exportRow transport replay provenance localName activeRead
      blockRead exportRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    activeReadingGateFields
        (ActiveReadingGateUp.mk target active retired blocking exportRow transport replay
          provenance localName) =
      [target, active, retired, blocking, exportRow, transport, replay, provenance,
        localName] →
      UnaryHistory target →
        UnaryHistory active →
          UnaryHistory retired →
            UnaryHistory blocking →
              UnaryHistory exportRow →
                UnaryHistory replay →
                  UnaryHistory localName →
                    Cont target active activeRead →
                      Cont activeRead blocking blockRead →
                        Cont blockRead exportRow exportRead →
                          Cont retired replay auditRead →
                            Cont exportRead localName publicRead →
                              PkgSig bundle publicRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row retired ∨ hsame row auditRead ∨
                                        hsame row exportRead ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      hsame row publicRead ∧ Cont retired replay auditRead ∧
                                        Cont blockRead exportRow exportRead ∧
                                          Cont exportRead localName publicRead ∧
                                            PkgSig bundle publicRead pkg)
                                    hsame ∧
                                  UnaryHistory auditRead ∧
                                    UnaryHistory exportRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _fieldsExact unaryTarget unaryActive unaryRetired unaryBlocking unaryExport unaryReplay
    unaryLocalName routeActive routeBlock routeExport routeAudit routePublic publicPkg
  have unaryActiveRead : UnaryHistory activeRead :=
    unary_cont_closed unaryTarget unaryActive routeActive
  have unaryBlockRead : UnaryHistory blockRead :=
    unary_cont_closed unaryActiveRead unaryBlocking routeBlock
  have unaryExportRead : UnaryHistory exportRead :=
    unary_cont_closed unaryBlockRead unaryExport routeExport
  have unaryAuditRead : UnaryHistory auditRead :=
    unary_cont_closed unaryRetired unaryReplay routeAudit
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryExportRead unaryLocalName routePublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row retired ∨ hsame row auditRead ∨ hsame row exportRead ∨
              hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont retired replay auditRead ∧
              Cont blockRead exportRow exportRead ∧ Cont exportRead localName publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, unaryPublicRead⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeAudit, routeExport, routePublic, publicPkg⟩
  }
  exact ⟨cert, unaryAuditRead, unaryExportRead, unaryPublicRead⟩

end BEDC.Derived.ActiveReadingGateUp
