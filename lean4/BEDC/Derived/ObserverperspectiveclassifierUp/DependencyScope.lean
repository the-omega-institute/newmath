import BEDC.Derived.ObserverperspectiveclassifierUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierDependencyScope [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name comparison publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont locality gap comparison ->
        Cont gap route publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row observerLeft ∨ hsame row observerRight ∨
                    hsame row universeLeft ∨ hsame row universeRight ∨
                      hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                        hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                          hsame row comparison ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont locality gap comparison ∧
                    Cont gap route publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory comparison ∧ UnaryHistory publicRead ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localityGapComparison gapRoutePublic publicPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, localityUnary, gapUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality,
    _localityTransport, _transportGap, _provenancePkg, namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed localityUnary gapUnary localityGapComparison
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed gapUnary routeUnary gapRoutePublic
  have sourceAtPublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
              hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row comparison ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont locality gap comparison ∧
              Cont gap route publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localityGapComparison, gapRoutePublic, publicPkg⟩
  }
  exact ⟨cert, comparisonUnary, publicUnary, namePkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
