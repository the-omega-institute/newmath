import BEDC.Derived.NestedIntervalCompactnessUp.TasteGate

namespace BEDC.Derived.NestedIntervalCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NestedIntervalCompactnessCarrier_prefix_readback_coverage [AskSetup] [PackageSetup]
    {I L D W R E H C P N prefixRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalCompactnessCarrier I L D W R E H C P N bundle pkg →
      Cont I D prefixRead →
        Cont prefixRead R readback →
          UnaryHistory prefixRead ∧ UnaryHistory readback ∧ Cont I D prefixRead ∧
            Cont prefixRead R readback ∧ hsame W (append I D) ∧
              hsame E (append W R) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier prefixRoute readbackRoute
  obtain ⟨iUnary, _lUnary, dUnary, _wUnary, rUnary, _hUnary, intervalRoute,
    realSealRoute, packageRead, _transportRoute, _nameRoute⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed iUnary dUnary prefixRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed prefixUnary rUnary readbackRoute
  exact
    ⟨prefixUnary, readbackUnary, prefixRoute, readbackRoute, intervalRoute,
      realSealRoute, packageRead⟩

end BEDC.Derived.NestedIntervalCompactnessUp
