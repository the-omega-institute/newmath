import BEDC.Derived.DyadicArchimedeanUp.L10Handoff

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

theorem DyadicArchimedeanStreamname_l10_handoff_transport [AskSetup] [PackageSetup]
    {source bound scale replay comparison enclosure transport route provenance localCert
      scaleRead comparisonRead enclosureRead l10Read streamRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicArchimedeanCarrier source bound scale replay comparison enclosure transport route
        provenance localCert bundle pkg ->
      Cont source scale scaleRead ->
        Cont scaleRead replay comparisonRead ->
          Cont comparisonRead enclosure enclosureRead ->
            Cont enclosureRead route l10Read ->
              PkgSig bundle l10Read pkg ->
                hsame streamRead l10Read ->
                  Cont streamRead transport consumerRead ->
                    UnaryHistory streamRead ∧ UnaryHistory consumerRead ∧
                      hsame streamRead l10Read ∧ Cont streamRead transport consumerRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle l10Read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier scaleRoute comparisonRoute enclosureRoute l10Route l10Pkg sameStream
    consumerRoute
  have l10Facts :=
    DyadicArchimedeanCarrier_l10_handoff carrier scaleRoute comparisonRoute enclosureRoute
      l10Route l10Pkg
  obtain
    ⟨_sourceUnary, _boundUnary, _scaleUnary, _replayUnary, _comparisonUnary,
      _enclosureUnary, _scaleReadUnary, _comparisonReadUnary, _enclosureReadUnary,
        l10Unary, _scaleRoute, _comparisonRoute, _enclosureRoute, _l10Route,
          provenancePkg, l10Pkg'⟩ := l10Facts
  have streamUnary : UnaryHistory streamRead :=
    unary_transport l10Unary (hsame_symm sameStream)
  have transportUnary : UnaryHistory transport := carrier.2.2.2.2.2.2.1
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed streamUnary transportUnary consumerRoute
  exact ⟨streamUnary, consumerUnary, sameStream, consumerRoute, provenancePkg, l10Pkg'⟩

end BEDC.Derived.DyadicArchimedeanUp
