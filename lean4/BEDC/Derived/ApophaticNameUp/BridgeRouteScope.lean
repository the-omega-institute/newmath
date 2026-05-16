import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_bridge_route_scope [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont route provenance bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row bridgeRead)
              (fun row : BHist =>
                hsame row bridgeRead ∧ UnaryHistory row ∧ Cont socket request gate ∧
                  Cont gate ledger route)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
                  hsame ledger (append request gate))
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory bridgeRead ∧ Cont socket request gate ∧
                Cont gate ledger route ∧ Cont route provenance bridgeRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeProvenanceBridge bridgePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute, gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceBridge
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row bridgeRead)
          (fun row : BHist =>
            hsame row bridgeRead ∧ UnaryHistory row ∧ Cont socket request gate ∧
              Cont gate ledger route)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
              hsame ledger (append request gate))
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro bridgeRead ⟨carrierPacket, hsame_refl bridgeRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        exact
          ⟨sourceRow.right, unary_transport bridgeUnary (hsame_symm sourceRow.right),
            socketRequestGate, gateLedgerRoute⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨provenancePkg, bridgePkg, ledgerSameRequestGate⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, bridgeUnary,
      socketRequestGate, gateLedgerRoute, routeProvenanceBridge, ledgerSameRequestGate,
      provenancePkg, bridgePkg⟩

end BEDC.Derived.ApophaticNameUp
