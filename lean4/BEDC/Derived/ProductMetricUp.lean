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

end BEDC.Derived.ProductMetricUp
