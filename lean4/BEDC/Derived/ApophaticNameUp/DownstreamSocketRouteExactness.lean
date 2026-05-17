import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_socket_route_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont socket request gate →
        Cont gate ledger nameRow →
          Cont nameRow provenance downstreamRead →
            PkgSig bundle downstreamRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row downstreamRead)
                  (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    Cont socket request gate ∧ Cont gate ledger nameRow ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                  UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧
                    Cont socket request gate ∧ Cont gate ledger nameRow ∧
                      Cont nameRow provenance downstreamRead ∧
                        hsame ledger (append request gate) ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketRequestGate gateLedgerNameRow nameProvenanceDownstream downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute, _gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed nameRowUnary provenanceUnary nameProvenanceDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row downstreamRead)
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket request gate ∧ Cont gate ledger nameRow ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro downstreamRead ⟨carrierPacket, hsame_refl downstreamRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact
        ⟨source.right, unary_transport downstreamUnary (hsame_symm source.right)⟩
    · intro _row _source
      exact ⟨socketRequestGate, gateLedgerNameRow, provenancePkg, downstreamPkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, downstreamUnary,
      socketRequestGate, gateLedgerNameRow, nameProvenanceDownstream, ledgerSameRequestGate,
      provenancePkg, downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp
