import BEDC.Derived.ProductMetricUp

/-!
# ProductMetricUp public Real classifier export.
-/

namespace BEDC.Derived.ProductMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProductMetricCarrier_real_classifier_public_export [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance localCert
      componentRead productRealRead publicDistance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      Cont leftDistance rightDistance componentRead ->
        Cont product componentRead productRealRead ->
          Cont product distance publicDistance ->
            PkgSig bundle productRealRead pkg ->
              PkgSig bundle publicDistance pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row productRealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row leftDistance ∨ hsame row rightDistance ∨ hsame row product ∨
                        hsame row distance ∨ hsame row transport ∨ hsame row componentRead ∨
                          hsame row productRealRead ∨ hsame row publicDistance)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont leftDistance rightDistance componentRead ∧
                        Cont product componentRead productRealRead ∧
                          Cont product distance publicDistance ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle productRealRead pkg ∧
                                PkgSig bundle publicDistance pkg)
                    hsame ∧ hsame distance componentRead ∧ hsame transport productRealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier componentReadRow productRealReadRow publicDistanceRow productRealReadPkg
    publicDistancePkg
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, _localCertUnary,
    productRow, distanceRow, transportRow, _routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row productRealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row leftDistance ∨ hsame row rightDistance ∨ hsame row product ∨
              hsame row distance ∨ hsame row transport ∨ hsame row componentRead ∨
                hsame row productRealRead ∨ hsame row publicDistance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont leftDistance rightDistance componentRead ∧
              Cont product componentRead productRealRead ∧
                Cont product distance publicDistance ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle productRealRead pkg ∧
                    PkgSig bundle publicDistance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro productRealRead ⟨hsame_refl productRealRead, productRealReadUnary⟩
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
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, componentReadRow, productRealReadRow, publicDistanceRow, provenancePkg,
          productRealReadPkg, publicDistancePkg⟩
  }
  exact ⟨cert, sameDistanceComponentRead, sameTransportProductRealRead⟩

end BEDC.Derived.ProductMetricUp
