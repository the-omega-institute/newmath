import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_refusal_gate_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow refusalRead →
        PkgSig bundle refusalRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row gate)
              (fun row : BHist => hsame row gate ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row gate ∧
                  Cont socket request gate ∧ Cont gate ledger nameRow)
              hsame ∧
            UnaryHistory gate ∧ UnaryHistory ledger ∧ Cont socket request gate ∧
              Cont gate ledger nameRow ∧ Cont ledger nameRow refusalRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRefusal refusalPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row gate)
          (fun row : BHist => hsame row gate ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row gate ∧
              Cont socket request gate ∧ Cont gate ledger nameRow)
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
      exact ⟨rowSameGate, unary_transport gateUnary (hsame_symm rowSameGate)⟩
    · intro row source
      exact ⟨provenancePkg, source.right, socketRequestGate, gateLedgerNameRow⟩
  exact
    ⟨cert, gateUnary, ledgerUnary, socketRequestGate, gateLedgerNameRow,
      ledgerNameRefusal, provenancePkg, refusalPkg⟩

end BEDC.Derived.ApophaticNameUp
