import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_ledger_downstream_coverage [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead downstreamExport :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont ledger nameRow downstreamRead →
        Cont downstreamRead provenance downstreamExport →
          PkgSig bundle downstreamExport pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧
                    hsame row downstreamExport)
                (fun row : BHist =>
                  hsame row ledger ∨ hsame row downstreamRead ∨ hsame row downstreamExport)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamExport pkg ∧
                    hsame row downstreamExport)
                hsame ∧
              UnaryHistory ledger ∧
              UnaryHistory downstreamRead ∧
              UnaryHistory downstreamExport ∧
              hsame ledger (append request gate) ∧
              Cont ledger nameRow downstreamRead ∧
              Cont downstreamRead provenance downstreamExport ∧
              PkgSig bundle provenance pkg ∧
              PkgSig bundle downstreamExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameDownstream downstreamProvenanceExport downstreamExportPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have downstreamExportUnary : UnaryHistory downstreamExport :=
    unary_cont_closed downstreamReadUnary provenanceUnary downstreamProvenanceExport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                bundle pkg ∧
              hsame row downstreamExport)
          (fun row : BHist =>
            hsame row ledger ∨ hsame row downstreamRead ∨ hsame row downstreamExport)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamExport pkg ∧
              hsame row downstreamExport)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro downstreamExport ⟨carrierPacket, hsame_refl downstreamExport⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact Or.inr (Or.inr source.right)
    · intro _row source
      exact ⟨provenancePkg, downstreamExportPkg, source.right⟩
  exact
    ⟨cert, ledgerUnary, downstreamReadUnary, downstreamExportUnary, ledgerSameRequestGate,
      ledgerNameDownstream, downstreamProvenanceExport, provenancePkg, downstreamExportPkg⟩

end BEDC.Derived.ApophaticNameUp
