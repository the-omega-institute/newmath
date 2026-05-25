import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberDyadicCoverRealRoute [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow streamRead regularRead
      realRead coverCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window route streamRead ->
        Cont streamRead provenance regularRead ->
          Cont regularRead nameRow realRead ->
            Cont realRead mesh coverCell ->
              PkgSig bundle coverCell pkg ->
                UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory realRead ∧ UnaryHistory coverCell ∧
                    Cont window route streamRead ∧
                      Cont streamRead provenance regularRead ∧
                        Cont regularRead nameRow realRead ∧
                          Cont realRead mesh coverCell ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle coverCell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRouteStream streamProvenanceRegular regularNameReal realMeshCoverCell
    coverCellPkg
  obtain ⟨_coverUnary, windowUnary, _radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary routeUnary windowRouteStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary provenanceUnary streamProvenanceRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed realUnary meshUnary realMeshCoverCell
  exact
    ⟨streamUnary, regularUnary, realUnary, coverCellUnary, windowRouteStream,
      streamProvenanceRegular, regularNameReal, realMeshCoverCell, provenancePkg,
      coverCellPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
