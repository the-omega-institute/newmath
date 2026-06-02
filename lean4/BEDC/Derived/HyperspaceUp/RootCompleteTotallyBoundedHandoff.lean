import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceRootCompleteTotallyBoundedHandoff [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M compactRead completionRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont X K0 compactRead ->
        Cont compactRead D0 completionRead ->
          Cont completionRead M rootRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle M pkg ->
                UnaryHistory compactRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory rootRead ∧ Cont X K0 compactRead ∧
                    Cont compactRead D0 completionRead ∧ Cont completionRead M rootRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle M pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier compactRoute completionRoute rootRoute provenancePkg namePkg
  obtain ⟨xUnary, k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, _d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, mUnary, _carrierPkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary k0Unary compactRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed compactUnary d0Unary completionRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed completionUnary mUnary rootRoute
  exact
    ⟨compactUnary, completionUnary, rootUnary, compactRoute, completionRoute, rootRoute,
      provenancePkg, namePkg⟩

end BEDC.Derived.HyperspaceUp
