import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_socket_citation_completeness
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citation endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request citation →
        Cont citation provenance endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row endpoint)
                (fun row : BHist =>
                  hsame row endpoint ∧ UnaryHistory row ∧ Cont socket request citation ∧
                    Cont citation provenance endpoint)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                    hsame row endpoint)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory citation ∧
                UnaryHistory endpoint ∧ Cont socket request citation ∧
                  Cont citation provenance endpoint ∧ hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestCitation citationProvenanceEndpoint endpointPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationUnary : UnaryHistory citation :=
    unary_cont_closed socketUnary requestUnary socketRequestCitation
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed citationUnary provenanceUnary citationProvenanceEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory row ∧ Cont socket request citation ∧
              Cont citation provenance endpoint)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
              hsame row endpoint)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro endpoint ⟨carrierPacket, hsame_refl endpoint⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport endpointUnary (hsame_symm source.right),
            socketRequestCitation, citationProvenanceEndpoint⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, endpointPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, citationUnary, endpointUnary, socketRequestCitation,
      citationProvenanceEndpoint, ledgerSameRequestGate⟩

end BEDC.Derived.ApophaticNameUp
