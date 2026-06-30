import BEDC.Derived.ObserverperspectiveclassifierUp.GapCommitmentReadback

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierComparisonRouteTotality [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name verdictRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route verdictRead →
        Cont verdictRead name publicRead →
          PkgSig bundle verdictRead pkg →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row observerLeft ∨ hsame row observerRight ∨
                      hsame row universeLeft ∨ hsame row universeRight ∨
                        hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                          hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                            hsame row verdictRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont gap route verdictRead ∧
                      Cont verdictRead name publicRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle publicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier gapRouteVerdict verdictNamePublic _verdictPkg publicReadPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      _localityUnary, gapUnary, _transportUnary, routeUnary, provenanceUnary, nameUnary,
      _observerUniverse, _universeLocality, _localityTransport, _transportGap,
      provenancePkg, _namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed gapUnary routeUnary gapRouteVerdict
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed verdictUnary nameUnary verdictNamePublic
  exact {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
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
      exact ⟨source.right, gapRouteVerdict, verdictNamePublic, provenancePkg, publicReadPkg⟩
  }

end BEDC.Derived.ObserverperspectiveclassifierUp
