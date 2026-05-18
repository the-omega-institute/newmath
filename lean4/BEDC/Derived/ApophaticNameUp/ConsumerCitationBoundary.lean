import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_consumer_citation_boundary [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow requestGate ledgerName
      citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont request gate requestGate →
        Cont ledger nameRow ledgerName →
          Cont requestGate ledger citationRead →
            PkgSig bundle citationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row citationRead)
                  (fun row : BHist =>
                    hsame row citationRead ∧ Cont request gate requestGate ∧
                      Cont requestGate ledger citationRead)
                  (fun row : BHist =>
                    hsame row citationRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle citationRead pkg)
                  hsame ∧
                UnaryHistory citationRead ∧
                Cont request gate requestGate ∧
                Cont requestGate ledger citationRead ∧
                hsame ledger (append request gate) ∧
                PkgSig bundle provenance pkg ∧
                PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateCont _ledgerNameCont requestGateLedgerCitation citationPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have requestGateUnary : UnaryHistory requestGate :=
    unary_cont_closed requestUnary gateUnary requestGateCont
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed requestGateUnary ledgerUnary requestGateLedgerCitation
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row citationRead)
          (fun row : BHist =>
            hsame row citationRead ∧ Cont request gate requestGate ∧
              Cont requestGate ledger citationRead)
          (fun row : BHist =>
            hsame row citationRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle citationRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro citationRead (And.intro carrierPacket (hsame_refl citationRead))
      · intro row _source
        exact hsame_refl row
      · intro _row _row' sameRows
        exact hsame_symm sameRows
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' sameRows sourceRow
        exact
          ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    · intro _row sourceRow
      exact ⟨sourceRow.right, requestGateCont, requestGateLedgerCitation⟩
    · intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, citationPkg⟩
  exact
    ⟨cert, citationUnary, requestGateCont, requestGateLedgerCitation, ledgerSameRequestGate,
      provenancePkg, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
