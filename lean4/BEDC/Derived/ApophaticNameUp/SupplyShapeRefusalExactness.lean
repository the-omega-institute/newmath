import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_supply_shape_refusal_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow supplyRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate supplyRead →
        Cont ledger nameRow ledgerRead →
          PkgSig bundle supplyRead pkg →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row request)
                  (fun row : BHist => hsame row request ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
                      PkgSig bundle ledgerRead pkg ∧ Cont request gate supplyRead ∧
                        Cont ledger nameRow ledgerRead)
                  hsame ∧
                UnaryHistory request ∧ UnaryHistory gate ∧ UnaryHistory supplyRead ∧
                  UnaryHistory ledgerRead ∧ Cont request gate supplyRead ∧
                    Cont ledger nameRow ledgerRead ∧ hsame ledger (append request gate) ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateSupply ledgerNameLedger supplyPkg ledgerPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  rcases carrier with
    ⟨_socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, _routeUnary,
      _provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed requestUnary gateUnary requestGateSupply
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameLedger
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
            bundle pkg ∧ hsame row request)
        (fun row : BHist => hsame row request ∧ UnaryHistory row)
        (fun _row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
            PkgSig bundle ledgerRead pkg ∧ Cont request gate supplyRead ∧
              Cont ledger nameRow ledgerRead)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro request (And.intro carrierPacket (hsame_refl request))
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    · intro row source
      exact And.intro source.right (unary_transport requestUnary (hsame_symm source.right))
    · intro row source
      exact
        ⟨provenancePkg, supplyPkg, ledgerPkg, requestGateSupply, ledgerNameLedger⟩
  exact
    ⟨cert, requestUnary, gateUnary, supplyReadUnary, ledgerReadUnary, requestGateSupply,
      ledgerNameLedger, ledgerSameRequestGate, provenancePkg⟩

end BEDC.Derived.ApophaticNameUp
