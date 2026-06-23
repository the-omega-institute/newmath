import BEDC.Derived.ObserverperspectiveclassifierUp.NameCertObligations

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierPublicReadbackCriterion [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap name readback →
        PkgSig bundle readback pkg →
          SemanticNameCert
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row observerLeft ∨ hsame row observerRight ∨
                  hsame row universeLeft ∨ hsame row universeRight ∨
                    hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                      hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row readback)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont observerLeft observerRight universeLeft ∧
                  Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
                    Cont transport route gap ∧ Cont gap name readback ∧
                      PkgSig bundle readback pkg)
              hsame ∧
            UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier gapNameReadback readbackPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      _localityUnary, gapUnary, _transportUnary, _routeUnary, _provenanceUnary,
      nameUnary, observerUniverse, universeLocality, localityTransport, transportGap,
      _provenancePkg, _namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed gapUnary nameUnary gapNameReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
              hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont observerLeft observerRight universeLeft ∧
              Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
                Cont transport route gap ∧ Cont gap name readback ∧
                  PkgSig bundle readback pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback
        ⟨hsame_refl readback, readbackUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, observerUniverse, universeLocality, localityTransport, transportGap,
          gapNameReadback, readbackPkg⟩
  }
  exact ⟨cert, readbackUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
