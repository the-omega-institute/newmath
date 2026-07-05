import BEDC.Derived.SubordinateModulusCoverUp.ScopedPackage

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubordinateModulusCoverPublicExport [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name compactRead pointwiseRead comparisonRead uniformRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont bundleSpine coverage compactRead →
        Cont centers pointwise pointwiseRead →
          Cont radii precision comparisonRead →
            Cont comparisonRead route uniformRead →
              Cont uniformRead name publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
                          hsame row precision ∨ hsame row pointwise ∨ hsame row coverage ∨
                            hsame row comparisons ∨ hsame row uniformRead ∨
                              hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont bundleSpine coverage compactRead ∧
                          Cont centers pointwise pointwiseRead ∧
                            Cont radii precision comparisonRead ∧
                              Cont comparisonRead route uniformRead ∧
                                Cont uniformRead name publicRead ∧
                                  PkgSig bundle publicRead pkg)
                      hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier compactRoute pointwiseRoute comparisonRoute uniformRoute publicRoute publicPkg
  obtain ⟨_eUnary, bundleUnary, centersUnary, radiiUnary, precisionUnary, pointwiseUnary,
    coverageUnary, _comparisonsUnary, _transportUnary, routeUnary, _provenanceUnary,
    nameUnary, _coverageRoute, _comparisonCarrierRoute, _provenancePkg, _namePkg⟩ :=
    carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleUnary coverageUnary compactRoute
  have pointwiseUnaryRead : UnaryHistory pointwiseRead :=
    unary_cont_closed centersUnary pointwiseUnary pointwiseRoute
  have comparisonUnaryRead : UnaryHistory comparisonRead :=
    unary_cont_closed radiiUnary precisionUnary comparisonRoute
  have uniformUnaryRead : UnaryHistory uniformRead :=
    unary_cont_closed comparisonUnaryRead routeUnary uniformRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed uniformUnaryRead nameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row pointwise ∨ hsame row coverage ∨
                hsame row comparisons ∨ hsame row uniformRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bundleSpine coverage compactRead ∧
              Cont centers pointwise pointwiseRead ∧ Cont radii precision comparisonRead ∧
                Cont comparisonRead route uniformRead ∧ Cont uniformRead name publicRead ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, pointwiseRoute, comparisonRoute, uniformRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.SubordinateModulusCoverUp
