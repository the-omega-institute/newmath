import BEDC.Derived.NestedIntervalCompactnessUp.TasteGate

namespace BEDC.Derived.NestedIntervalCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NestedIntervalCompactnessCarrier_located_dyadic_scope [AskSetup] [PackageSetup]
    {I L D W R E H C P N locatedRead meshRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalCompactnessCarrier I L D W R E H C P N bundle pkg →
      Cont I L locatedRead →
        Cont locatedRead D meshRead →
          Cont meshRead W windowRead →
            UnaryHistory I ∧ UnaryHistory L ∧ UnaryHistory D ∧
              UnaryHistory locatedRead ∧ UnaryHistory meshRead ∧ UnaryHistory windowRead ∧
                Cont I L locatedRead ∧ Cont locatedRead D meshRead ∧
                  Cont meshRead W windowRead ∧ hsame W (append I D) ∧
                    hsame E (append W R) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame ProbeBundle Pkg PkgSig
  intro carrier locatedRoute meshRoute windowRoute
  obtain ⟨iUnary, lUnary, dUnary, wUnary, _rUnary, _hUnary, intervalRoute,
    realSealRoute, packageRead, _transportRoute, _nameRoute⟩ := carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed iUnary lUnary locatedRoute
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed locatedUnary dUnary meshRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed meshUnary wUnary windowRoute
  exact
    ⟨iUnary, lUnary, dUnary, locatedUnary, meshUnary, windowUnary, locatedRoute,
      meshRoute, windowRoute, intervalRoute, realSealRoute, packageRead⟩

end BEDC.Derived.NestedIntervalCompactnessUp
