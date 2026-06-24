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

theorem observer_perspective_classifier_cross_alignment_locality_soundness_namecert
    [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route provenance
      name comparison alignmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont locality gap comparison →
        Cont comparison route alignmentRead →
          PkgSig bundle alignmentRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row locality ∨ hsame row gap ∨ hsame row comparison ∨
                      hsame row alignmentRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                    hsame row comparison ∨ hsame row route ∨ hsame row alignmentRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont locality gap comparison ∧
                    Cont comparison route alignmentRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle alignmentRead pkg)
                hsame ∧
              UnaryHistory comparison ∧ UnaryHistory alignmentRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localityGapComparison comparisonRouteAlignment alignmentPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      localityUnary, gapUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      _observerUniverse, _universeLocality, _localityTransport, _transportGap,
      provenancePkg, namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed localityUnary gapUnary localityGapComparison
  have alignmentUnary : UnaryHistory alignmentRead :=
    unary_cont_closed comparisonUnary routeUnary comparisonRouteAlignment
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row locality ∨ hsame row gap ∨ hsame row comparison ∨
                hsame row alignmentRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
              hsame row comparison ∨ hsame row route ∨ hsame row alignmentRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont locality gap comparison ∧
              Cont comparison route alignmentRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle alignmentRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro alignmentRead
          ⟨Or.inr (Or.inr (Or.inr (hsame_refl alignmentRead))), alignmentUnary⟩
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
        constructor
        · cases source.left with
          | inl sameLocality =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLocality)
          | inr rest =>
              cases rest with
              | inl sameGap =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameGap))
              | inr rest =>
                  cases rest with
                  | inl sameComparison =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameComparison)))
                  | inr sameAlignment =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameAlignment)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLocality =>
          exact Or.inl sameLocality
      | inr rest =>
          cases rest with
          | inl sameGap =>
              exact Or.inr (Or.inl sameGap)
          | inr rest =>
              cases rest with
              | inl sameComparison =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl sameComparison)))
              | inr sameAlignment =>
                  exact
                    Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr sameAlignment))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, localityGapComparison, comparisonRouteAlignment, provenancePkg,
          namePkg, alignmentPkg⟩
  }
  exact ⟨cert, comparisonUnary, alignmentUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
