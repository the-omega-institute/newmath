import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_supply_shape_noninternalization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont request gate supplyRead →
        PkgSig bundle supplyRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row request)
              (fun row : BHist => hsame row request ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
                  hsame row request ∧ Cont request gate supplyRead)
              hsame ∧
            UnaryHistory request ∧ UnaryHistory supplyRead ∧ Cont request gate supplyRead ∧
              PkgSig bundle supplyRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier requestGateSupply supplyPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, requestUnary, gateUnary, _ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have supplyUnary : UnaryHistory supplyRead :=
    unary_cont_closed requestUnary gateUnary requestGateSupply
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
      have rowSameRequest : hsame row request := source.right
      exact ⟨rowSameRequest, unary_transport requestUnary (hsame_symm rowSameRequest)⟩
    · intro row source
      exact ⟨provenancePkg, supplyPkg, source.right, requestGateSupply⟩
  exact ⟨cert, requestUnary, supplyUnary, requestGateSupply, supplyPkg⟩

end BEDC.Derived.ApophaticNameUp
