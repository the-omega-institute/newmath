import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleRouteNonexport [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      Cont localName supply auditRead ->
        PkgSig bundle auditRead pkg ->
          UnaryHistory localName ∧ UnaryHistory supply ∧ UnaryHistory auditRead ∧
            Cont mode witness route ∧ Cont route supply localName ∧
              Cont localName supply auditRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier localSupplyAudit auditPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    localUnary, _transportSame, modeWitnessRoute, routeSupplyLocal, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed localUnary supplyUnary localSupplyAudit
  exact
    ⟨localUnary, supplyUnary, auditUnary, modeWitnessRoute, routeSupplyLocal,
      localSupplyAudit, provenancePkg, auditPkg⟩

theorem AxiomDependencyTupleSupplyModeDisjointness [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      (hsame mode BHist.Empty ∨ hsame mode (BHist.e0 BHist.Empty) ∨
          hsame mode (BHist.e1 BHist.Empty)) ∧
        (hsame mode BHist.Empty -> hsame mode (BHist.e0 BHist.Empty) -> False) ∧
          (hsame mode BHist.Empty -> hsame mode (BHist.e1 BHist.Empty) -> False) ∧
            (hsame mode (BHist.e0 BHist.Empty) ->
              hsame mode (BHist.e1 BHist.Empty) -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨modeCases, _modeUnary, _witnessUnary, _supplyUnary, _transportUnary, _routeUnary,
    _localUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocal, _provenancePkg⟩ :=
      carrier
  constructor
  · exact modeCases
  · constructor
    · intro modeEmpty modeZero
      cases modeEmpty
      cases modeZero
    · constructor
      · intro modeEmpty modeOne
        cases modeEmpty
        cases modeOne
      · intro modeZero modeOne
        cases modeZero
        cases modeOne

end BEDC.Derived.AxiomDependencyTupleUp
