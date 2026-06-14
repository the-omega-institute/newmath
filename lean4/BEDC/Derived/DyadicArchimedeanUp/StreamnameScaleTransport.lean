import BEDC.Derived.DyadicArchimedeanUp.NameCertObligations

namespace BEDC.Derived.DyadicArchimedeanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicArchimedeanStreamnameScaleTransport [AskSetup] [PackageSetup]
    {dyadic stream scale transported route provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic ->
      UnaryHistory stream ->
        Cont dyadic stream scale ->
          hsame transported scale ->
            Cont transported stream route ->
              PkgSig bundle provenance pkg ->
                UnaryHistory scale ∧ UnaryHistory transported ∧ UnaryHistory route ∧
                  hsame transported scale ∧ Cont dyadic stream scale ∧
                    Cont transported stream route ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro dyadicUnary streamUnary scaleRoute sameTransported routeCont provenancePkg
  have scaleUnary : UnaryHistory scale :=
    unary_cont_closed dyadicUnary streamUnary scaleRoute
  have transportedUnary : UnaryHistory transported :=
    unary_transport scaleUnary (hsame_symm sameTransported)
  have routeUnary : UnaryHistory route :=
    unary_cont_closed transportedUnary streamUnary routeCont
  exact
    ⟨scaleUnary, transportedUnary, routeUnary, sameTransported, scaleRoute, routeCont,
      provenancePkg⟩

end BEDC.Derived.DyadicArchimedeanUp
