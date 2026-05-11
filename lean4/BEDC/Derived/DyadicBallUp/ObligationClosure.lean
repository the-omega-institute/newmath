import BEDC.Derived.DyadicBallUp

namespace BEDC.Derived.DyadicBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicBallFiniteCarrier_obligation_closure [AskSetup] [PackageSetup]
    {center radius schedule observation containment route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicBallFiniteCarrier center radius schedule observation containment route provenance
        nameRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row containment ∨ hsame row route ∨ hsame row nameRow)
          (fun row : BHist =>
            hsame row containment ∨ hsame row route ∨ hsame row nameRow)
          (fun row : BHist =>
            hsame row containment ∨ hsame row route ∨ hsame row nameRow)
          hsame ∧
        UnaryHistory containment ∧ UnaryHistory route ∧ UnaryHistory nameRow ∧
          Cont center radius containment ∧ Cont schedule observation route ∧
            Cont route provenance nameRow ∧ PkgSig bundle nameRow pkg := by
  intro carrier
  obtain ⟨_centerUnary, _radiusUnary, _scheduleUnary, _observationUnary, containmentUnary,
    routeUnary, _provenanceUnary, nameRowUnary, containmentRow, routeRow, nameRowRoute,
    pkgRow⟩ := carrier
  have visibleCert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row containment ∨ hsame row route ∨ hsame row nameRow)
          (fun row : BHist =>
            hsame row containment ∨ hsame row route ∨ hsame row nameRow)
          (fun row : BHist =>
            hsame row containment ∨ hsame row route ∨ hsame row nameRow)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro containment (Or.inl (hsame_refl containment))
      equiv_refl := by
        intro row _visible
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows visible
        cases visible with
        | inl sameContainment =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameContainment)
        | inr rest =>
            cases rest with
            | inl sameRoute =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRoute))
            | inr sameNameRow =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameNameRow))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨visibleCert, containmentUnary, routeUnary, nameRowUnary, containmentRow, routeRow,
      nameRowRoute, pkgRow⟩

end BEDC.Derived.DyadicBallUp
