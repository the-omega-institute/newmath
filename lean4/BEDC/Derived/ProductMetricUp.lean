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

theorem ProductMetricCarrier_projection_non_escape [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory leftDistance ∧
            UnaryHistory rightDistance ∧ UnaryHistory product ∧ UnaryHistory leftRead ∧
              UnaryHistory rightRead ∧ Cont left right product ∧ Cont left product leftRead ∧
                Cont right product rightRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier leftProjection rightProjection
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, _distanceRow, _transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftUnary productUnary leftProjection
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightUnary productUnary rightProjection
  exact
    ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, productUnary,
      leftReadUnary, rightReadUnary, productRow, leftProjection, rightProjection, provenancePkg⟩

theorem ProductMetricCarrier_component_diagonal_boundary [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      diagonalRead leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          Cont leftRead rightRead diagonalRead ->
            UnaryHistory leftRead ∧ UnaryHistory rightRead ∧ UnaryHistory diagonalRead ∧
              Cont left product leftRead ∧ Cont right product rightRead ∧
                Cont leftRead rightRead diagonalRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier leftProjection rightProjection diagonalRoute
  obtain ⟨leftUnary, rightUnary, _leftDistanceUnary, _rightDistanceUnary, _localCertUnary,
    productRow, _distanceRow, _transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftUnary productUnary leftProjection
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightUnary productUnary rightProjection
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed leftReadUnary rightReadUnary diagonalRoute
  exact
    ⟨leftReadUnary, rightReadUnary, diagonalReadUnary, leftProjection, rightProjection,
      diagonalRoute, provenancePkg⟩

theorem ProductMetricCarrier_distance_ledger_triangle_route [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont distance transport triangleRead ->
        UnaryHistory distance ∧ UnaryHistory transport ∧ UnaryHistory triangleRead ∧
          Cont product distance transport ∧ Cont distance transport triangleRead ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier triangleRoute
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed distanceUnary transportUnary triangleRoute
  exact
    ⟨distanceUnary, transportUnary, triangleReadUnary, transportRow, triangleRoute,
      provenancePkg⟩

theorem ProductMetricCarrier_distance_ledger_scope [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      componentRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont leftDistance rightDistance componentRead ->
        Cont product componentRead scopedRead ->
          PkgSig bundle scopedRead pkg ->
            UnaryHistory leftDistance ∧ UnaryHistory rightDistance ∧
              UnaryHistory componentRead ∧ UnaryHistory scopedRead ∧
                hsame distance componentRead ∧ hsame transport scopedRead ∧
                  Cont leftDistance rightDistance distance ∧
                    Cont leftDistance rightDistance componentRead ∧
                      Cont product componentRead scopedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier componentReadRow scopedReadRow scopedReadPkg
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have componentReadUnary : UnaryHistory componentRead :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary componentReadRow
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed productUnary componentReadUnary scopedReadRow
  have sameDistanceComponentRead : hsame distance componentRead :=
    cont_respects_hsame (hsame_refl leftDistance) (hsame_refl rightDistance) distanceRow
      componentReadRow
  have sameTransportScopedRead : hsame transport scopedRead :=
    cont_respects_hsame (hsame_refl product) sameDistanceComponentRead transportRow
      scopedReadRow
  exact
    ⟨leftDistanceUnary, rightDistanceUnary, componentReadUnary, scopedReadUnary,
      sameDistanceComponentRead, sameTransportScopedRead, distanceRow, componentReadRow,
      scopedReadRow, provenancePkg, scopedReadPkg⟩

theorem ProductMetricCarrier_metricspace_obligation_package [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      leftRead rightRead triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          Cont distance transport triangleRead ->
            UnaryHistory product ∧ UnaryHistory distance ∧ UnaryHistory transport ∧
              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧ UnaryHistory triangleRead ∧
                Cont left right product ∧ Cont leftDistance rightDistance distance ∧
                  Cont product distance transport ∧ Cont left product leftRead ∧
                    Cont right product rightRead ∧ Cont distance transport triangleRead ∧
                      hsame product (append left right) ∧
                        hsame distance (append leftDistance rightDistance) ∧
                          hsame transport (append product distance) ∧
                            hsame triangleRead (append distance transport) ∧
                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier leftProjection rightProjection triangleRoute
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftUnary productUnary leftProjection
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightUnary productUnary rightProjection
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed distanceUnary transportUnary triangleRoute
  exact
    ⟨productUnary, distanceUnary, transportUnary, leftReadUnary, rightReadUnary,
      triangleReadUnary, productRow, distanceRow, transportRow, leftProjection, rightProjection,
      triangleRoute, productRow, distanceRow, transportRow, triangleRoute, provenancePkg⟩

theorem ProductMetricCarrier_metricspace_anchor [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      leftRead rightRead triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          Cont distance transport triangleRead ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row product ∨ hsame row distance ∨ hsame row transport ∨
                    hsame row leftRead ∨ hsame row rightRead ∨ hsame row triangleRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row left ∨ hsame row right ∨ hsame row leftDistance ∨
                    hsame row rightDistance ∨ hsame row product ∨ hsame row distance ∨
                      hsame row transport ∨ hsame row leftRead ∨ hsame row rightRead ∨
                        hsame row triangleRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont left right product ∧
                    Cont leftDistance rightDistance distance ∧ Cont product distance transport ∧
                      Cont left product leftRead ∧ Cont right product rightRead ∧
                        Cont distance transport triangleRead ∧ PkgSig bundle provenance pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro carrier leftProjection rightProjection triangleRoute
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftUnary productUnary leftProjection
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightUnary productUnary rightProjection
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed distanceUnary transportUnary triangleRoute
  have sourceProduct :
      (fun row : BHist =>
        (hsame row product ∨ hsame row distance ∨ hsame row transport ∨
          hsame row leftRead ∨ hsame row rightRead ∨ hsame row triangleRead) ∧
          UnaryHistory row) product := by
    exact ⟨Or.inl (hsame_refl product), productUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro product sourceProduct
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row other sameRows source
        have sourceOther :
            hsame other product ∨ hsame other distance ∨ hsame other transport ∨
              hsame other leftRead ∨ hsame other rightRead ∨ hsame other triangleRead := by
          cases source.left with
          | inl sameProduct =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameProduct)
          | inr rest =>
              cases rest with
              | inl sameDistance =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDistance))
              | inr rest =>
                  cases rest with
                  | inl sameTransport =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameTransport)))
                  | inr rest =>
                      cases rest with
                      | inl sameLeftRead =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameLeftRead))))
                      | inr rest =>
                          cases rest with
                          | inl sameRightRead =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows)
                                            sameRightRead)))))
                          | inr sameTriangleRead =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm sameRows)
                                            sameTriangleRead)))))
        exact ⟨sourceOther, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameProduct =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameProduct))))
      | inr rest =>
          cases rest with
          | inl sameDistance =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDistance)))))
          | inr rest =>
              cases rest with
              | inl sameTransport =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inl sameTransport))))))
              | inr rest =>
                  cases rest with
                  | inl sameLeftRead =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl sameLeftRead)))))))
                  | inr rest =>
                      cases rest with
                      | inl sameRightRead =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inl sameRightRead))))))))
                      | inr sameTriangleRead =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr sameTriangleRead))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, productRow, distanceRow, transportRow, leftProjection, rightProjection,
          triangleRoute, provenancePkg⟩
  }

theorem ProductMetricCarrier_realup_consumer_package [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      componentRead productRealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont leftDistance rightDistance componentRead ->
        Cont product componentRead productRealRead ->
          PkgSig bundle productRealRead pkg ->
            UnaryHistory product ∧ UnaryHistory distance ∧ UnaryHistory componentRead ∧
              UnaryHistory productRealRead ∧ hsame distance componentRead ∧
                hsame transport productRealRead ∧ Cont product distance transport ∧
                  Cont product componentRead productRealRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle productRealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier componentReadRow productRealReadRow productRealReadPkg
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have componentReadUnary : UnaryHistory componentRead :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary componentReadRow
  have productRealReadUnary : UnaryHistory productRealRead :=
    unary_cont_closed productUnary componentReadUnary productRealReadRow
  have sameDistanceComponentRead : hsame distance componentRead :=
    cont_respects_hsame (hsame_refl leftDistance) (hsame_refl rightDistance) distanceRow
      componentReadRow
  have sameTransportProductRealRead : hsame transport productRealRead :=
    cont_respects_hsame (hsame_refl product) sameDistanceComponentRead transportRow
      productRealReadRow
  exact
    ⟨productUnary, distanceUnary, componentReadUnary, productRealReadUnary,
      sameDistanceComponentRead, sameTransportProductRealRead, transportRow, productRealReadRow,
      provenancePkg, productRealReadPkg⟩

theorem ProductMetricCarrier_scoped_dependency_package [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      leftRead rightRead triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont left product leftRead ->
        Cont right product rightRead ->
          Cont distance transport triangleRead ->
            SemanticNameCert
                (fun row : BHist => hsame row triangleRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row left ∨ hsame row right ∨ hsame row leftDistance ∨
                    hsame row rightDistance ∨ hsame row product ∨ hsame row distance ∨
                      hsame row transport ∨ hsame row triangleRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont left right product ∧
                    Cont leftDistance rightDistance distance ∧ Cont product distance transport ∧
                      Cont distance transport triangleRead ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                UnaryHistory triangleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier leftProjection rightProjection triangleRoute
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftUnary productUnary leftProjection
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightUnary productUnary rightProjection
  have triangleReadUnary : UnaryHistory triangleRead :=
    unary_cont_closed distanceUnary transportUnary triangleRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row triangleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row leftDistance ∨
              hsame row rightDistance ∨ hsame row product ∨ hsame row distance ∨
                hsame row transport ∨ hsame row triangleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont left right product ∧
              Cont leftDistance rightDistance distance ∧ Cont product distance transport ∧
                Cont distance transport triangleRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro triangleRead ⟨hsame_refl triangleRead, triangleReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, productRow, distanceRow, transportRow, triangleRoute,
          provenancePkg⟩
  }
  exact ⟨cert, leftReadUnary, rightReadUnary, triangleReadUnary⟩

theorem ProductMetricCarrier_public_metricspace_export [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      publicDistance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont product distance publicDistance ->
        PkgSig bundle publicDistance pkg ->
          UnaryHistory product ∧ UnaryHistory distance ∧ UnaryHistory transport ∧
            UnaryHistory publicDistance ∧ hsame transport publicDistance ∧
              Cont left right product ∧ Cont leftDistance rightDistance distance ∧
                Cont product distance transport ∧ Cont product distance publicDistance ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicDistance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier publicDistanceRoute publicDistancePkg
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have publicDistanceUnary : UnaryHistory publicDistance :=
    unary_cont_closed productUnary distanceUnary publicDistanceRoute
  have sameTransportPublicDistance : hsame transport publicDistance :=
    cont_respects_hsame (hsame_refl product) (hsame_refl distance) transportRow
      publicDistanceRoute
  exact
    ⟨productUnary, distanceUnary, transportUnary, publicDistanceUnary,
      sameTransportPublicDistance, productRow, distanceRow, transportRow,
      publicDistanceRoute, provenancePkg, publicDistancePkg⟩

end BEDC.Derived.ProductMetricUp
