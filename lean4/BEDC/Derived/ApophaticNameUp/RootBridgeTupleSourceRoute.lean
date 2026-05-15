import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_bridge_tuple_source_route_totality
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead handoff :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow downstreamRead →
        Cont downstreamRead route handoff →
          PkgSig bundle handoff pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row ledger)
                (fun row : BHist =>
                  hsame row ledger ∧ UnaryHistory row ∧ Cont ledger nameRow downstreamRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg ∧
                    hsame row ledger ∧ Cont downstreamRead route handoff)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                UnaryHistory ledger ∧ UnaryHistory downstreamRead ∧ UnaryHistory handoff ∧
                  Cont ledger nameRow downstreamRead ∧ Cont downstreamRead route handoff ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameDownstream downstreamRouteHandoff handoffPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ :=
    carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed downstreamUnary routeUnary downstreamRouteHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist =>
            hsame row ledger ∧ UnaryHistory row ∧ Cont ledger nameRow downstreamRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg ∧
              hsame row ledger ∧ Cont downstreamRead route handoff)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
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
          ⟨source.right, unary_transport ledgerUnary (hsame_symm source.right),
            ledgerNameDownstream⟩
      ledger_sound := by
        intro _row source
        exact
          ⟨provenancePkg, handoffPkg, source.right, downstreamRouteHandoff⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, downstreamUnary,
      handoffUnary, ledgerNameDownstream, downstreamRouteHandoff, provenancePkg,
      handoffPkg⟩

end BEDC.Derived.ApophaticNameUp
