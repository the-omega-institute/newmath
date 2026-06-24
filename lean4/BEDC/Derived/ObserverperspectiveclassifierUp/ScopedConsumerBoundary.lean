import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierScopedConsumerBoundary [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route publicRead →
        Cont publicRead name verdict →
          PkgSig bundle publicRead pkg →
            PkgSig bundle verdict pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row verdict ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row observerLeft ∨ hsame row observerRight ∨
                      hsame row universeLeft ∨ hsame row universeRight ∨
                        hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                          hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                            hsame row publicRead ∨ hsame row verdict)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont gap route publicRead ∧
                      Cont publicRead name verdict ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg ∧
                          PkgSig bundle verdict pkg)
                  hsame ∧
                UnaryHistory publicRead ∧ UnaryHistory verdict := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier gapRoutePublicRead publicReadNameVerdict publicReadPkg verdictPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, _localityUnary, gapUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameUnary, _observerUniverse, _universeLocality, _localityTransport,
    _transportGap, provenancePkg, namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed gapUnary routeUnary gapRoutePublicRead
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed publicReadUnary nameUnary publicReadNameVerdict
  let SourceSpec : BHist → Prop := fun row => hsame row verdict ∧ UnaryHistory row
  let PatternSpec : BHist → Prop := fun row =>
    hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
      hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
        hsame row route ∨ hsame row provenance ∨ hsame row name ∨ hsame row publicRead ∨
          hsame row verdict
  let LedgerPolicy : BHist → Prop := fun row =>
    UnaryHistory row ∧ Cont gap route publicRead ∧ Cont publicRead name verdict ∧
      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
        PkgSig bundle publicRead pkg ∧ PkgSig bundle verdict pkg
  have sourceVerdict : SourceSpec verdict :=
    ⟨hsame_refl verdict, verdictUnary⟩
  have cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy hsame :=
    { core :=
        { carrier_inhabited := ⟨verdict, sourceVerdict⟩
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
            intro _row other sameRows sourceRow
            exact
              ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
                unary_transport sourceRow.right sameRows⟩ }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, gapRoutePublicRead, publicReadNameVerdict, provenancePkg,
            namePkg, publicReadPkg, verdictPkg⟩ }
  exact ⟨cert, publicReadUnary, verdictUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
