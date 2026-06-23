import BEDC.Derived.ObserverperspectiveclassifierUp.NameCertObligations

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierGapCommitmentReadback [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name verdictRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont gap route verdictRead ->
        PkgSig bundle verdictRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row verdictRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row observerLeft ∨ hsame row observerRight ∨
                  hsame row universeLeft ∨ hsame row universeRight ∨
                    hsame row locality ∨ hsame row gap ∨ hsame row verdictRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont gap route verdictRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle verdictRead pkg)
              hsame ∧
            UnaryHistory gap ∧ UnaryHistory verdictRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier gapRouteVerdict verdictPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      _localityUnary, gapUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      _observerUniverse, _universeLocality, _localityTransport, _transportGap,
      provenancePkg, _namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed gapUnary routeUnary gapRouteVerdict
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row verdictRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
              hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨
                hsame row verdictRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont gap route verdictRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle verdictRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro verdictRead
        ⟨hsame_refl verdictRead, verdictUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gapRouteVerdict, provenancePkg, verdictPkg⟩
  }
  exact ⟨cert, gapUnary, verdictUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
