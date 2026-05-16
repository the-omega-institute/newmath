import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_boundary_citation_universal_factorization
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow citation →
        Cont citation provenance endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                    bundle pkg ∧
                  hsame row endpoint)
              (fun row : BHist =>
                Cont socket request gate ∧ Cont gate ledger nameRow ∧
                  Cont ledger nameRow citation ∧ Cont citation provenance row ∧
                    PkgSig bundle endpoint pkg)
              (fun row : BHist =>
                UnaryHistory row ∧ hsame ledger (append request gate) ∧
                  PkgSig bundle endpoint pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameCitation citationProvenanceEndpoint endpointPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  rcases carrier with
    ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary, _routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute, _gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩
  have citationUnary : UnaryHistory citation :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameCitation
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed citationUnary provenanceUnary citationProvenanceEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrierPacket (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨socketRequestGate, gateLedgerNameRow, ledgerNameCitation,
          cont_result_hsame_transport citationProvenanceEndpoint (hsame_symm source.right),
          endpointPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.right), ledgerSameRequestGate,
          endpointPkg⟩
  }

end BEDC.Derived.ApophaticNameUp
