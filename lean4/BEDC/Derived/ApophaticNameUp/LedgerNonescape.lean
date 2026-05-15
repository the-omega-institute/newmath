import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger route exported →
        PkgSig bundle exported pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row ledger ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg)
              (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket request gate ∧ Cont gate ledger route ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory exported ∧ Cont socket request gate ∧
                Cont gate ledger route ∧ Cont ledger route exported ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerRouteExported exportedPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteExported
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledger ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket request gate ∧ Cont gate ledger route ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨hsame_refl ledger, carrierPacket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro _row source
      exact ⟨source.left, unary_transport ledgerUnary (hsame_symm source.left)⟩
    · intro _row _source
      exact ⟨socketRequestGate, gateLedgerRoute, provenancePkg, exportedPkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, exportedUnary,
      socketRequestGate, gateLedgerRoute, ledgerRouteExported, ledgerSameRequestGate,
      provenancePkg, exportedPkg⟩

end BEDC.Derived.ApophaticNameUp
