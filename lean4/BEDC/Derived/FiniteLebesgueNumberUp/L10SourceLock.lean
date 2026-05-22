import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberL10SourceLock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow streamRead regularRead realRead
      meshRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius streamRead ->
        Cont streamRead route regularRead ->
          Cont regularRead mesh realRead ->
            Cont realRead cover meshRead ->
              Cont meshRead nameRow compactRead ->
                PkgSig bundle compactRead pkg ->
                  UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory realRead ∧ UnaryHistory meshRead ∧
                      UnaryHistory compactRead ∧ Cont window radius streamRead ∧
                        Cont streamRead route regularRead ∧
                          Cont regularRead mesh realRead ∧
                            Cont realRead cover meshRead ∧
                              Cont meshRead nameRow compactRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRadiusStream streamRouteRegular regularMeshReal realCoverMesh
    meshNameCompact compactPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary meshUnary regularMeshReal
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed realUnary coverUnary realCoverMesh
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed meshReadUnary nameRowUnary meshNameCompact
  exact
    ⟨streamUnary, regularUnary, realUnary, meshReadUnary, compactUnary,
      windowRadiusStream, streamRouteRegular, regularMeshReal, realCoverMesh,
      meshNameCompact, provenancePkg, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
