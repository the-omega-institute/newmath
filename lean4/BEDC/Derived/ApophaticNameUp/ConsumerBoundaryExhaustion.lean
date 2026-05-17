import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_consumer_boundary_exhaustion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow consumerRead →
        PkgSig bundle consumerRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row consumerRead)
              (fun row : BHist =>
                hsame row consumerRead ∧ UnaryHistory row ∧ Cont ledger nameRow consumerRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                  hsame row consumerRead)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory consumerRead ∧ Cont socket request gate ∧
                Cont gate ledger nameRow ∧ Cont ledger nameRow consumerRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameConsumer consumerPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row consumerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ UnaryHistory row ∧ Cont ledger nameRow consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨carrierPacket, hsame_refl consumerRead⟩
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
          ⟨source.right, unary_transport consumerUnary (hsame_symm source.right),
            ledgerNameConsumer⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, consumerPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, consumerUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameConsumer, ledgerSameRequestGate,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.ApophaticNameUp
