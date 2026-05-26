import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_stdbridge_premise_strict_obstruction
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow bridgeRead
      obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow bridgeRead →
        PkgSig bundle bridgeRead pkg →
          Cont bridgeRead ledger obstructionRead →
            PkgSig bundle obstructionRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route
                      provenance nameRow bundle pkg ∧ hsame row nameRow)
                  (fun row : BHist => hsame row nameRow ∧ Cont ledger nameRow bridgeRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
                      Cont bridgeRead ledger obstructionRead)
                  hsame ∧
                UnaryHistory bridgeRead ∧ UnaryHistory obstructionRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle bridgeRead pkg ∧
                    PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameBridge bridgePkg bridgeLedgerObstruction obstructionPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBridge
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed bridgeUnary ledgerUnary bridgeLedgerObstruction
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ Cont ledger nameRow bridgeRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
              Cont bridgeRead ledger obstructionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
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
        exact ⟨source.right, ledgerNameBridge⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, source.right, bridgeLedgerObstruction⟩
    }
  exact
    ⟨cert, bridgeUnary, obstructionUnary, ledgerSameRequestGate, bridgePkg,
      obstructionPkg⟩

end BEDC.Derived.ApophaticNameUp
