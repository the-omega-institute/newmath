import BEDC.Derived.ProductMetricUp

/-!
# ProductMetricUp bridge certificates.
-/

namespace BEDC.Derived.ProductMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProductMetricCarrier_real_classifier_bridge [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      componentRead productRealRead triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont leftDistance rightDistance componentRead ->
        Cont product componentRead productRealRead ->
          Cont distance transport triangleRead ->
            PkgSig bundle productRealRead pkg ->
              UnaryHistory product ∧ UnaryHistory distance ∧ UnaryHistory componentRead ∧
                UnaryHistory productRealRead ∧ UnaryHistory triangleRead ∧
                  hsame distance componentRead ∧ hsame transport productRealRead ∧
                    Cont product distance transport ∧ Cont product componentRead productRealRead ∧
                      Cont distance transport triangleRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle productRealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier componentReadRow productRealReadRow triangleReadRow productRealReadPkg
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have componentReadUnary : UnaryHistory componentRead :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary componentReadRow
  have productRealReadUnary : UnaryHistory productRealRead :=
    unary_cont_closed productUnary componentReadUnary productRealReadRow
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed distanceUnary transportUnary triangleReadRow
  have sameDistanceComponentRead : hsame distance componentRead :=
    cont_respects_hsame (hsame_refl leftDistance) (hsame_refl rightDistance) distanceRow
      componentReadRow
  have sameTransportProductRealRead : hsame transport productRealRead :=
    cont_respects_hsame (hsame_refl product) sameDistanceComponentRead transportRow
      productRealReadRow
  exact
    ⟨productUnary, distanceUnary, componentReadUnary, productRealReadUnary, triangleReadUnary,
      sameDistanceComponentRead, sameTransportProductRealRead, transportRow, productRealReadRow,
      triangleReadRow, provenancePkg, productRealReadPkg⟩

theorem ProductMetricCarrier_standard_metricspace_bridge_certificate [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      leftRead rightRead triangleRead componentRead productRealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          Cont distance transport triangleRead ->
            Cont leftDistance rightDistance componentRead ->
              Cont product componentRead productRealRead ->
                PkgSig bundle productRealRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row triangleRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row left ∨ hsame row right ∨ hsame row leftDistance ∨
                          hsame row rightDistance ∨ hsame row product ∨ hsame row distance ∨
                            hsame row transport ∨ hsame row triangleRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont left right product ∧
                          Cont leftDistance rightDistance distance ∧
                            Cont product distance transport ∧
                              Cont distance transport triangleRead ∧
                                PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                      UnaryHistory triangleRead ∧ hsame transport productRealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro carrier leftProjection rightProjection triangleReadRow componentReadRow
    productRealReadRow productRealReadPkg
  obtain ⟨cert, leftReadUnary, rightReadUnary, triangleReadUnary⟩ :=
    ProductMetricCarrier_scoped_dependency_package carrier leftProjection rightProjection
      triangleReadRow
  obtain ⟨_productUnary, _distanceUnary, _componentReadUnary, _productRealReadUnary,
    _triangleUnary, _sameDistanceComponentRead, sameTransportProductRealRead, _transportRow,
    _productRealReadRow, _triangleReadRow, _provenancePkg, _productRealReadPkg⟩ :=
      ProductMetricCarrier_real_classifier_bridge carrier componentReadRow productRealReadRow
        triangleReadRow productRealReadPkg
  exact ⟨cert, leftReadUnary, rightReadUnary, triangleReadUnary, sameTransportProductRealRead⟩

end BEDC.Derived.ProductMetricUp
