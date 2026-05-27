import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_diameter_consumer_handoff [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead diameterRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead replay diameterRead ->
            PkgSig bundle diameterRead pkg ->
              UnaryHistory X ∧ UnaryHistory S ∧ UnaryHistory center ∧ UnaryHistory radius ∧
                UnaryHistory ball ∧ UnaryHistory memberRead ∧ UnaryHistory ballRead ∧
                  UnaryHistory diameterRead ∧ Cont S center memberRead ∧
                    Cont memberRead radius ballRead ∧ Cont ballRead replay diameterRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle diameterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier subsetCenter memberRadius ballReplayDiameter diameterPkg
  obtain ⟨xUnary, sUnary, centerUnary, radiusUnary, ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have diameterUnary : UnaryHistory diameterRead :=
    unary_cont_closed ballReadUnary replayUnary ballReplayDiameter
  exact
    ⟨xUnary, sUnary, centerUnary, radiusUnary, ballUnary, memberUnary, ballReadUnary,
      diameterUnary, subsetCenter, memberRadius, ballReplayDiameter, provenancePkg,
      diameterPkg⟩

end BEDC.Derived.BoundedSetUp
