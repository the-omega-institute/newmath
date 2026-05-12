import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# ProductMetricUp finite carrier surface.
-/

namespace BEDC.Derived.ProductMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ProductMetricCarrier [AskSetup] [PackageSetup]
    (left right leftDistance rightDistance product distance transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory leftDistance ∧
    UnaryHistory rightDistance ∧ UnaryHistory localCert ∧ Cont left right product ∧
      Cont leftDistance rightDistance distance ∧ Cont product distance transport ∧
        Cont transport provenance route ∧ PkgSig bundle provenance pkg ∧
          SemanticNameCert
            (fun row : BHist => hsame row localCert)
            (fun row : BHist => hsame row localCert)
            (fun row : BHist => hsame row localCert)
            hsame

theorem ProductMetricCarrier_classifier_stability [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      left' right' leftDistance' rightDistance' product' distance' transport' route'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame leftDistance leftDistance' ->
            hsame rightDistance rightDistance' ->
              Cont left' right' product' ->
                Cont leftDistance' rightDistance' distance' ->
                  Cont product' distance' transport' ->
                    Cont transport' provenance' route' ->
                      PkgSig bundle provenance' pkg ->
                        ProductMetricCarrier left' right' leftDistance' rightDistance' product'
                            distance' transport' route' provenance' localCert bundle pkg ∧
                          hsame product product' ∧ hsame distance distance' ∧
                            hsame transport transport' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameLeft sameRight sameLeftDistance sameRightDistance productRow'
    distanceRow' transportRow' routeRow' provenancePkg'
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, _provenancePkg, nameCert⟩ := carrier
  have leftUnary' : UnaryHistory left' :=
    unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory right' :=
    unary_transport rightUnary sameRight
  have leftDistanceUnary' : UnaryHistory leftDistance' :=
    unary_transport leftDistanceUnary sameLeftDistance
  have rightDistanceUnary' : UnaryHistory rightDistance' :=
    unary_transport rightDistanceUnary sameRightDistance
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameLeft sameRight productRow productRow'
  have sameDistance : hsame distance distance' :=
    cont_respects_hsame sameLeftDistance sameRightDistance distanceRow distanceRow'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameProduct sameDistance transportRow transportRow'
  have transported :
      ProductMetricCarrier left' right' leftDistance' rightDistance' product' distance'
        transport' route' provenance' localCert bundle pkg :=
    ⟨leftUnary', rightUnary', leftDistanceUnary', rightDistanceUnary', localCertUnary,
      productRow', distanceRow', transportRow', routeRow', provenancePkg', nameCert⟩
  exact And.intro transported
    (And.intro sameProduct
      (And.intro sameDistance sameTransport))

theorem ProductMetricCarrier_component_distance_transport [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      componentRead productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont leftDistance rightDistance componentRead ->
        Cont product componentRead productRead ->
          UnaryHistory componentRead ∧ UnaryHistory productRead ∧ hsame distance componentRead ∧
            Cont product componentRead productRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier componentReadRow productReadRow
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, _transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have componentReadUnary : UnaryHistory componentRead :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary componentReadRow
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed productUnary componentReadUnary productReadRow
  have sameDistanceComponentRead : hsame distance componentRead :=
    cont_respects_hsame (hsame_refl leftDistance) (hsame_refl rightDistance) distanceRow
      componentReadRow
  exact
    ⟨componentReadUnary, productReadUnary, sameDistanceComponentRead, productReadRow,
      provenancePkg⟩

theorem ProductMetricCarrier_projection_route_exactness [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          hsame product (append left right) ∧ hsame leftRead (append left (append left right)) ∧
            hsame rightRead (append right (append left right)) ∧ UnaryHistory leftRead ∧
              UnaryHistory rightRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier leftProjection rightProjection
  obtain ⟨leftUnary, rightUnary, _leftDistanceUnary, _rightDistanceUnary, _localCertUnary,
    productRow, _distanceRow, _transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftUnary productUnary leftProjection
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightUnary productUnary rightProjection
  have leftReadSame : hsame leftRead (append left (append left right)) := by
    cases leftProjection
    cases productRow
    rfl
  have rightReadSame : hsame rightRead (append right (append left right)) := by
    cases rightProjection
    cases productRow
    rfl
  exact
    ⟨productRow, leftReadSame, rightReadSame, leftReadUnary, rightReadUnary, provenancePkg⟩

end BEDC.Derived.ProductMetricUp
