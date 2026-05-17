import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_gate_route_locality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead
      downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont gate ledger gateRead →
        Cont gateRead route downstreamRead →
          PkgSig bundle downstreamRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row gate)
                (fun row : BHist =>
                  hsame row gate ∧ UnaryHistory row ∧ Cont gate ledger gateRead)
                (fun _row : BHist =>
                  Cont gate ledger gateRead ∧ Cont gateRead route downstreamRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg)
                hsame ∧
              UnaryHistory gateRead ∧ UnaryHistory downstreamRead ∧
                Cont gate ledger gateRead ∧ Cont gateRead route downstreamRead ∧
                  PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gateLedgerRead gateReadRouteDownstream downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ :=
    carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed gateReadUnary routeUnary gateReadRouteDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row gate)
          (fun row : BHist =>
            hsame row gate ∧ UnaryHistory row ∧ Cont gate ledger gateRead)
          (fun _row : BHist =>
            Cont gate ledger gateRead ∧ Cont gateRead route downstreamRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle downstreamRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gate ⟨carrierPacket, hsame_refl gate⟩
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
        ⟨source.right, unary_transport gateUnary (hsame_symm source.right),
          gateLedgerRead⟩
    · intro _row _source
      exact
        ⟨gateLedgerRead, gateReadRouteDownstream, provenancePkg, downstreamPkg⟩
  exact
    ⟨cert, gateReadUnary, downstreamUnary, gateLedgerRead, gateReadRouteDownstream,
      downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp
