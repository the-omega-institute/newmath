import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootDyadicRadiusObligation [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRadius streamRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover mesh dyadicRadius ->
        Cont dyadicRadius window streamRead ->
          Cont streamRead route realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory cover ∧ UnaryHistory mesh ∧ UnaryHistory radius ∧
                UnaryHistory dyadicRadius ∧ UnaryHistory streamRead ∧
                  UnaryHistory realRead ∧ Cont cover mesh dyadicRadius ∧
                    Cont dyadicRadius window streamRead ∧ Cont streamRead route realRead ∧
                      Cont radius mesh route ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverMeshDyadic dyadicWindowStream streamRouteReal realPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRadius :=
    unary_cont_closed coverUnary meshUnary coverMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed streamUnary routeUnary streamRouteReal
  exact
    ⟨coverUnary, meshUnary, radiusUnary, dyadicUnary, streamUnary, realUnary,
      coverMeshDyadic, dyadicWindowStream, streamRouteReal, radiusMeshRoute, provenancePkg,
      realPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
