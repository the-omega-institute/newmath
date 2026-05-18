import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_supply_request_consumer_factorization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow supplyRead ledgerRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont request gate supplyRead ->
        Cont ledger nameRow ledgerRead ->
          Cont ledgerRead route consumerRead ->
            PkgSig bundle supplyRead pkg ->
              PkgSig bundle consumerRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      ApophaticNameCarrier socket request gate ledger transport route provenance
                        nameRow bundle pkg ∧ hsame row request)
                    (fun row : BHist => hsame row request ∧ UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
                        hsame row request ∧ Cont request gate supplyRead)
                    hsame ∧
                  UnaryHistory request ∧ UnaryHistory supplyRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory consumerRead ∧ Cont request gate supplyRead ∧
                      Cont ledger nameRow ledgerRead ∧ Cont ledgerRead route consumerRead ∧
                        hsame ledger (append request gate) ∧
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateSupply ledgerNameRead ledgerReadRoute supplyPkg consumerPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have supplyUnary : UnaryHistory supplyRead :=
    unary_cont_closed requestUnary gateUnary requestGateSupply
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRead
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row request)
          (fun row : BHist => hsame row request ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
              hsame row request ∧ Cont request gate supplyRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro request ⟨carrierPacket, hsame_refl request⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, unary_transport requestUnary (hsame_symm source.right)⟩
    · intro row source
      exact ⟨provenancePkg, supplyPkg, source.right, requestGateSupply⟩
  exact
    ⟨cert, requestUnary, supplyUnary, ledgerReadUnary, consumerUnary, requestGateSupply,
      ledgerNameRead, ledgerReadRoute, ledgerSameRequestGate, consumerPkg⟩

end BEDC.Derived.ApophaticNameUp
