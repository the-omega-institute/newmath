import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCarrier_observation_cut_stability [AskSetup] [PackageSetup]
    {k W D R H C P N cutWindow cutDyadic cutRegular observed replay
      structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FinitePrefixStreamCarrier k W D R H C P N →
      UnaryHistory cutWindow →
        UnaryHistory cutDyadic →
          UnaryHistory cutRegular →
            Cont k cutWindow observed →
              Cont observed cutDyadic replay →
                Cont H C structuralRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      UnaryHistory k ∧ UnaryHistory cutWindow ∧ UnaryHistory cutDyadic ∧
                        UnaryHistory observed ∧ UnaryHistory replay ∧
                          UnaryHistory structuralRead ∧ Cont k cutWindow observed ∧
                            Cont observed cutDyadic replay ∧ Cont H C structuralRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: FinitePrefixStreamCarrier BHist Cont ProbeBundle PkgSig
  intro carrier cutWindowUnary cutDyadicUnary _cutRegularUnary observedRoute replayRoute
    structuralRoute provenancePkg localNamePkg
  obtain ⟨depthUnary, _windowUnary, dyadicUnary, regularUnary, comparisonUnary,
    _nameUnary, _sameStructural, handoffRoute, _replayRoute, _namedRoute⟩ := carrier
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed depthUnary cutWindowUnary observedRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed observedUnary cutDyadicUnary replayRoute
  have structuralBaseUnary : UnaryHistory H :=
    unary_cont_closed dyadicUnary regularUnary handoffRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed structuralBaseUnary comparisonUnary structuralRoute
  exact
    ⟨depthUnary, cutWindowUnary, cutDyadicUnary, observedUnary, replayUnary,
      structuralUnary, observedRoute, replayRoute, structuralRoute, provenancePkg,
      localNamePkg⟩

end BEDC.Derived.FinitePrefixStreamUp
