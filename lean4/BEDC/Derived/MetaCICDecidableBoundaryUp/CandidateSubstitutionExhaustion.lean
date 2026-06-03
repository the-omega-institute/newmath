import BEDC.Derived.MetaCICDecidableBoundaryUp.SiblingProvenance

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundaryCandidateSubstitutionExhaustion [AskSetup] [PackageSetup]
    {T S B F R H C P N candidateRead substitutionRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg →
      Cont B F candidateRead →
        Cont candidateRead H substitutionRead →
          Cont substitutionRead R replayRead →
            PkgSig bundle replayRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                      hsame row R ∨ hsame row candidateRead ∨
                        hsame row substitutionRead ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle replayRead pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory substitutionRead ∧
                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier candidateRoute substitutionRoute replayRoute replayPkg
  obtain ⟨tUnary, sUnary, fUnary, rUnary, hUnary, _cUnary, pUnary, _nUnary,
    checkerStructuralBounded, provenancePkg, _localNamePkg⟩ := carrier
  have boundedUnary : UnaryHistory B :=
    unary_cont_closed tUnary sUnary checkerStructuralBounded
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed boundedUnary fUnary candidateRoute
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed candidateUnary hUnary substitutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed substitutionUnary rUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
              hsame row candidateRead ∨ hsame row substitutionRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, replayPkg⟩
  }
  exact ⟨cert, candidateUnary, substitutionUnary, replayUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
