import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberSourceChainAdmission [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow stream regular real
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius stream ->
        Cont stream mesh regular ->
          Cont regular route real ->
            Cont route nameRow rootRead ->
              PkgSig bundle real pkg ->
                PkgSig bundle rootRead pkg ->
                  UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
                    UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory real ∧
                      UnaryHistory rootRead ∧ Cont cover radius stream ∧
                        Cont stream mesh regular ∧ Cont regular route real ∧
                          Cont route nameRow rootRead ∧ PkgSig bundle real pkg ∧
                            PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRadiusStream streamMeshRegular regularRouteReal routeNameRoot
    realPkg rootPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory stream :=
    unary_cont_closed coverUnary radiusUnary coverRadiusStream
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed streamUnary meshUnary streamMeshRegular
  have realUnary : UnaryHistory real :=
    unary_cont_closed regularUnary routeUnary regularRouteReal
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  exact
    ⟨coverUnary, radiusUnary, meshUnary, streamUnary, regularUnary, realUnary, rootUnary,
      coverRadiusStream, streamMeshRegular, regularRouteReal, routeNameRoot, realPkg, rootPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
