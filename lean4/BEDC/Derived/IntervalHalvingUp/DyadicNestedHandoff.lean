import BEDC.Derived.IntervalHalvingUp

namespace BEDC.Derived.IntervalHalvingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem interval_halving_dyadic_nested_handoff_carrier_route [AskSetup] [PackageSetup]
    {left right midpoint chosenHalf radius streamWindow regularReadback realSeal transport replay
      provenance localName dyadicRead nestedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalHalvingCarrier left right midpoint chosenHalf radius streamWindow regularReadback
        realSeal transport replay provenance localName bundle pkg ->
      Cont left radius dyadicRead ->
        Cont dyadicRead streamWindow nestedRead ->
          PkgSig bundle nestedRead pkg ->
            UnaryHistory left ∧ UnaryHistory radius ∧ UnaryHistory streamWindow ∧
              UnaryHistory dyadicRead ∧ UnaryHistory nestedRead ∧
                Cont left radius dyadicRead ∧ Cont dyadicRead streamWindow nestedRead ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle nestedRead pkg := by
  -- BEDC touchpoint anchor: IntervalHalvingCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicRoute nestedRoute nestedPkg
  obtain
    ⟨leftUnary, _rightUnary, _midpointUnary, _chosenHalfUnary, radiusUnary,
      streamWindowUnary, _regularReadbackUnary, _realSealUnary, _transportUnary,
      _transportAnchor, _midpointRoute, _radiusRoute, _readbackRoute, _realSealRoute,
      _provenanceRoute, _provenancePkg, packageRoute⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed leftUnary radiusUnary dyadicRoute
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed dyadicUnary streamWindowUnary nestedRoute
  exact
    ⟨leftUnary, radiusUnary, streamWindowUnary, dyadicUnary, nestedUnary, dyadicRoute,
      nestedRoute, packageRoute, nestedPkg⟩

end BEDC.Derived.IntervalHalvingUp
