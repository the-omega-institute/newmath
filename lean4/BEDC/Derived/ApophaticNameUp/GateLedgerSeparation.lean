import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_gate_ledger_separation [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont gate ledger gateRead →
        PkgSig bundle gateRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row gate)
              (fun row : BHist => hsame row gate ∧ UnaryHistory row ∧
                Cont socket request gate)
              (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row gate ∧
                hsame ledger (append request gate))
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory gateRead ∧
            Cont socket request gate ∧ Cont gate ledger gateRead ∧
            hsame ledger (append request gate) ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle gateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gateLedgerRead gateReadPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row gate)
          (fun row : BHist => hsame row gate ∧ UnaryHistory row ∧
            Cont socket request gate)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row gate ∧
            hsame ledger (append request gate))
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gate ⟨carrierPacket, hsame_refl gate⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameGate : hsame row gate := source.right
      exact
        ⟨rowSameGate, unary_transport gateUnary (hsame_symm rowSameGate),
          socketRequestGate⟩
    · intro row source
      exact ⟨provenancePkg, source.right, ledgerSameRequestGate⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, gateReadUnary,
      socketRequestGate, gateLedgerRead, ledgerSameRequestGate, provenancePkg, gateReadPkg⟩

end BEDC.Derived.ApophaticNameUp
