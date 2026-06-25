import BEDC.Derived.SubordinateModulusCoverUp.LedgerExactness

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubordinateModulusCoverObligationClosureRoute [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name coverageRead pointwiseRead comparisonRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont centers coverage coverageRead →
        Cont centers pointwise pointwiseRead →
          Cont radii precision comparisonRead →
            Cont comparisonRead route uniformRead →
              PkgSig bundle coverageRead pkg →
                PkgSig bundle pointwiseRead pkg →
                  PkgSig bundle comparisonRead pkg →
                    PkgSig bundle uniformRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
                              hsame row precision ∨ hsame row coverage ∨
                                hsame row pointwise ∨ hsame row comparisons ∨
                                  hsame row uniformRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont centers coverage coverageRead ∧
                              Cont centers pointwise pointwiseRead ∧
                                Cont radii precision comparisonRead ∧
                                  Cont comparisonRead route uniformRead ∧
                                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                                      PkgSig bundle uniformRead pkg)
                          hsame ∧
                        UnaryHistory coverageRead ∧ UnaryHistory pointwiseRead ∧
                          UnaryHistory comparisonRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier centersCoverageRead centersPointwiseRead radiiPrecisionRead
    comparisonRouteRead _coverageReadPkg _pointwiseReadPkg _comparisonReadPkg uniformReadPkg
  obtain ⟨_eUnary, _bundleSpineUnary, centersUnary, radiiUnary, precisionUnary,
    pointwiseUnary, coverageUnary, _comparisonsUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _coverageRoute, _comparisonRoute, provenancePkg,
    namePkg⟩ := carrier
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed centersUnary coverageUnary centersCoverageRead
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed centersUnary pointwiseUnary centersPointwiseRead
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed radiiUnary precisionUnary radiiPrecisionRead
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed comparisonReadUnary routeUnary comparisonRouteRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row coverage ∨ hsame row pointwise ∨
                hsame row comparisons ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont centers coverage coverageRead ∧
              Cont centers pointwise pointwiseRead ∧ Cont radii precision comparisonRead ∧
                Cont comparisonRead route uniformRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨uniformRead, ⟨hsame_refl uniformRead, uniformReadUnary⟩⟩
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
          Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, centersCoverageRead, centersPointwiseRead, radiiPrecisionRead,
          comparisonRouteRead, provenancePkg, namePkg, uniformReadPkg⟩
  }
  exact
    ⟨cert, coverageReadUnary, pointwiseReadUnary, comparisonReadUnary, uniformReadUnary⟩

end BEDC.Derived.SubordinateModulusCoverUp
