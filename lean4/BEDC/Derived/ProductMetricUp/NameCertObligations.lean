import BEDC.Derived.ProductMetricUp

namespace BEDC.Derived.ProductMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProductMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {left right leftDistance rightDistance product distance transport route provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg ->
      UnaryHistory provenance ->
        Cont route localCert consumer ->
          PkgSig bundle consumer pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row localCert ∧
                    ProductMetricCarrier left right leftDistance rightDistance product distance
                      transport route provenance localCert bundle pkg)
                (fun row : BHist =>
                  hsame row left ∨ hsame row right ∨ hsame row product ∨ hsame row distance ∨
                    hsame row transport ∨ hsame row route ∨ hsame row localCert)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧
                    hsame row localCert)
                hsame ∧
              UnaryHistory product ∧ UnaryHistory distance ∧ UnaryHistory transport ∧
                UnaryHistory route ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier provenanceUnary consumerRoute consumerPkg
  have carrierWitness :
      ProductMetricCarrier left right leftDistance rightDistance product distance transport route
        provenance localCert bundle pkg :=
    carrier
  obtain ⟨leftUnary, rightUnary, leftDistanceUnary, rightDistanceUnary, localCertUnary,
    productRow, distanceRow, transportRow, routeRow, provenancePkg, _nameCert⟩ := carrier
  have productUnary : UnaryHistory product :=
    unary_cont_closed leftUnary rightUnary productRow
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed leftDistanceUnary rightDistanceUnary distanceRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed productUnary distanceUnary transportRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed transportUnary provenanceUnary routeRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary localCertUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localCert ∧
              ProductMetricCarrier left right leftDistance rightDistance product distance
                transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row product ∨ hsame row distance ∨
              hsame row transport ∨ hsame row route ∨ hsame row localCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧ hsame row localCert)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localCert ⟨hsame_refl localCert, carrierWitness⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact ⟨cert, productUnary, distanceUnary, transportUnary, routeUnary, consumerUnary⟩

end BEDC.Derived.ProductMetricUp
