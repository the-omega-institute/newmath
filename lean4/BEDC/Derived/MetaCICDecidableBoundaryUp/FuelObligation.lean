import BEDC.Derived.MetaCICDecidableBoundaryUp.SiblingProvenance

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundaryFuelObligation [AskSetup] [PackageSetup]
    {T S B F R H C P N boundedRead fuelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg ->
      Cont B F boundedRead ->
        Cont F R fuelRead ->
          PkgSig bundle fuelRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row fuelRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                    hsame row R ∨ hsame row fuelRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont B F boundedRead ∧ Cont F R fuelRead ∧
                    PkgSig bundle fuelRead pkg)
                hsame ∧
              UnaryHistory boundedRead ∧ UnaryHistory fuelRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier boundedRoute fuelRoute fuelPkg
  obtain ⟨checkerUnary, structuralUnary, finishedUnary, refusalUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, checkerStructuralBounded,
    _provenancePkg, _localNamePkg⟩ := carrier
  have boundedUnary : UnaryHistory B :=
    unary_cont_closed checkerUnary structuralUnary checkerStructuralBounded
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed boundedUnary finishedUnary boundedRoute
  have fuelReadUnary : UnaryHistory fuelRead :=
    unary_cont_closed finishedUnary refusalUnary fuelRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fuelRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
              hsame row R ∨ hsame row fuelRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B F boundedRead ∧ Cont F R fuelRead ∧
              PkgSig bundle fuelRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fuelRead ⟨hsame_refl fuelRead, fuelReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundedRoute, fuelRoute, fuelPkg⟩
  }
  exact ⟨cert, boundedReadUnary, fuelReadUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
