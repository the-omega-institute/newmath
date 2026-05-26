import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberDyadicCoverCellSelection [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow streamRead regularRead realRead
      coverCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window transport streamRead ->
        Cont streamRead route regularRead ->
          Cont regularRead mesh realRead ->
            Cont realRead nameRow coverCell ->
              PkgSig bundle coverCell pkg ->
                UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory realRead ∧ UnaryHistory coverCell ∧
                    Cont window transport streamRead ∧
                      Cont streamRead route regularRead ∧
                        Cont regularRead mesh realRead ∧
                          Cont realRead nameRow coverCell ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle coverCell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowTransportStream streamRouteRegular regularMeshReal realNameCover
    coverCellPkg
  obtain ⟨_coverUnary, windowUnary, _radiusUnary, meshUnary, transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary transportUnary windowTransportStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary meshUnary regularMeshReal
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed realUnary nameRowUnary realNameCover
  exact
    ⟨streamUnary, regularUnary, realUnary, coverCellUnary, windowTransportStream,
      streamRouteRegular, regularMeshReal, realNameCover, provenancePkg, coverCellPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
