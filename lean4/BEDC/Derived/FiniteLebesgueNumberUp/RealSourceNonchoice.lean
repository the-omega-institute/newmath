import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRealSourceNonchoice [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow streamRead regularRead
      realRead meshRead coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window route streamRead ->
        Cont streamRead radius regularRead ->
          Cont regularRead nameRow realRead ->
            Cont realRead mesh meshRead ->
              Cont meshRead cover coverRead ->
                PkgSig bundle coverRead pkg ->
                  UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory realRead ∧ UnaryHistory meshRead ∧
                      UnaryHistory coverRead ∧ Cont window route streamRead ∧
                        Cont streamRead radius regularRead ∧
                          Cont regularRead nameRow realRead ∧ Cont realRead mesh meshRead ∧
                            Cont meshRead cover coverRead ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle coverRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowRouteStream streamRadiusRegular regularNameReal realMeshRead
    meshCoverRead coverPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary routeUnary windowRouteStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary radiusUnary streamRadiusRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed realUnary meshUnary realMeshRead
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed meshReadUnary coverUnary meshCoverRead
  exact
    ⟨streamUnary, regularUnary, realUnary, meshReadUnary, coverReadUnary, windowRouteStream,
      streamRadiusRegular, regularNameReal, realMeshRead, meshCoverRead, provenancePkg,
      coverPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
