import BEDC.Derived.DyadicMidpointUp

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicMidpointRadiusHalvingWindow [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      radiusRead leftChild rightChild : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      Cont scale midpoint radiusRead ->
        Cont left midpoint leftChild ->
          Cont midpoint right rightChild ->
            PkgSig bundle radiusRead pkg ->
              UnaryHistory radiusRead ∧ UnaryHistory leftChild ∧ UnaryHistory rightChild ∧
                Cont scale midpoint radiusRead ∧ Cont left midpoint leftChild ∧
                  Cont midpoint right rightChild ∧ hsame midpoint (append scale (append left right)) ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: DyadicMidpointCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier radiusRoute leftChildRoute rightChildRoute radiusPkg
  obtain ⟨leftUnary, rightUnary, scaleUnary, midpointUnary, _branchUnary, _windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, midpointRow, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed scaleUnary midpointUnary radiusRoute
  have leftChildUnary : UnaryHistory leftChild :=
    unary_cont_closed leftUnary midpointUnary leftChildRoute
  have rightChildUnary : UnaryHistory rightChild :=
    unary_cont_closed midpointUnary rightUnary rightChildRoute
  exact
    ⟨radiusUnary, leftChildUnary, rightChildUnary, radiusRoute, leftChildRoute,
      rightChildRoute, midpointRow, endpointPkg, radiusPkg⟩

end BEDC.Derived.DyadicMidpointUp
