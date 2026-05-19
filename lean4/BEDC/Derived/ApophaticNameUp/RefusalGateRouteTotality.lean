import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_gate_route_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead routeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont request gate gateRead ->
        Cont gate ledger routeRead ->
          PkgSig bundle gateRead pkg ->
            PkgSig bundle routeRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route
                        provenance nameRow bundle pkg /\
                      hsame row routeRead)
                  (fun row : BHist =>
                    hsame row gate \/ hsame row ledger \/ hsame row routeRead)
                  (fun _row : BHist =>
                    Cont request gate gateRead /\ Cont gate ledger routeRead /\
                      PkgSig bundle provenance pkg /\ PkgSig bundle routeRead pkg)
                  hsame /\
                UnaryHistory gateRead /\ UnaryHistory routeRead /\
                  hsame ledger (append request gate) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier gateRoute routeLedger gatePkg routePkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate,
    _requestGateRoute, _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate,
    provenancePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed requestUnary gateUnary gateRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed gateUnary ledgerUnary routeLedger
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg /\
              hsame row routeRead)
          (fun row : BHist =>
            hsame row gate \/ hsame row ledger \/ hsame row routeRead)
          (fun _row : BHist =>
            Cont request gate gateRead /\ Cont gate ledger routeRead /\
              PkgSig bundle provenance pkg /\ PkgSig bundle routeRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro routeRead ⟨carrierPacket, hsame_refl routeRead⟩
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
        exact Or.inr (Or.inr source.right)
      ledger_sound := by
        intro _row _source
        exact ⟨gateRoute, routeLedger, provenancePkg, routePkg⟩
    }
  exact ⟨cert, gateReadUnary, routeReadUnary, ledgerSameRequestGate⟩

end BEDC.Derived.ApophaticNameUp
