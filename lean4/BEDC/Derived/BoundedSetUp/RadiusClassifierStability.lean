import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_radius_classifier_stability [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow radiusPrime memberRead ballRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      hsame radius radiusPrime ->
        Cont S center memberRead ->
          Cont memberRead radiusPrime ballRead ->
            PkgSig bundle ballRead pkg ->
              UnaryHistory radiusPrime ∧ UnaryHistory memberRead ∧ UnaryHistory ballRead ∧
                Cont S center memberRead ∧ Cont memberRead radiusPrime ballRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ballRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier radiusSame memberRoute ballRoute ballPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have radiusPrimeUnary : UnaryHistory radiusPrime :=
    unary_transport radiusUnary radiusSame
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary memberRoute
  have ballUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusPrimeUnary ballRoute
  exact
    ⟨radiusPrimeUnary, memberUnary, ballUnary, memberRoute, ballRoute, provenancePkg,
      ballPkg⟩

end BEDC.Derived.BoundedSetUp
