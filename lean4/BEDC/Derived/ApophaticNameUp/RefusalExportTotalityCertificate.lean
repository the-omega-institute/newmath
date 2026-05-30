import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameRefusalExportTotality [AskSetup] [PackageSetup]
    {socket request gate ledger transport continuation provenance localName publicRead
      exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport continuation provenance
        localName bundle pkg →
      Cont socket request publicRead →
        Cont publicRead ledger exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row socket ∨ hsame row request ∨ hsame row gate ∨
                    hsame row ledger ∨ hsame row transport ∨ hsame row continuation ∨
                      hsame row exportRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle exportRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory publicRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier socketRequestPublic publicLedgerExport exportReadPkg
  obtain ⟨socketUnary, requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _continuationUnary, _provenanceUnary, _localNameUnary, _socketRequestGate,
    _requestGateContinuation, _gateLedgerContinuation, _gateLedgerLocalName,
    _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed socketUnary requestUnary socketRequestPublic
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed publicUnary ledgerUnary publicLedgerExport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row socket ∨ hsame row request ∨ hsame row gate ∨ hsame row ledger ∨
              hsame row transport ∨ hsame row continuation ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle exportRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exportReadPkg, provenancePkg⟩
  }
  exact ⟨cert, publicUnary, exportUnary⟩

end BEDC.Derived.ApophaticNameUp
