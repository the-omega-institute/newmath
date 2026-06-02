import BEDC.Derived.MetaCICDecidableBoundaryUp.SiblingProvenance

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundaryFuelWindowReplay [AskSetup] [PackageSetup]
    {T S B F R H C P N boundedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg →
      Cont B F boundedRead →
        Cont boundedRead C replayRead →
          PkgSig bundle replayRead pkg →
            UnaryHistory boundedRead ∧
              UnaryHistory replayRead ∧
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row replayRead ∧
                      MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                      hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row boundedRead ∨ hsame row replayRead)
                  (fun row : BHist =>
                    hsame row replayRead ∧ Cont B F boundedRead ∧
                      Cont boundedRead C replayRead ∧ PkgSig bundle replayRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier boundedRoute replayRoute replayPkg
  have carrierWhole := carrier
  obtain ⟨tUnary, sUnary, fUnary, _rUnary, _hUnary, cUnary, _pUnary, _nUnary,
    checkerStructuralBounded, _provenancePkg, _localNamePkg⟩ := carrier
  have boundedUnary : UnaryHistory B :=
    unary_cont_closed tUnary sUnary checkerStructuralBounded
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed boundedUnary fUnary boundedRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundedReadUnary cUnary replayRoute
  have sourceReplay :
      (fun row : BHist =>
        hsame row replayRead ∧
          MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg) replayRead := by
    exact ⟨hsame_refl replayRead, carrierWhole⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row replayRead ∧
            MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg)
        (fun row : BHist =>
          hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row boundedRead ∨ hsame row replayRead)
        (fun row : BHist =>
          hsame row replayRead ∧ Cont B F boundedRead ∧
            Cont boundedRead C replayRead ∧ PkgSig bundle replayRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
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
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundedRoute, replayRoute, replayPkg⟩
  }
  exact ⟨boundedReadUnary, replayReadUnary, cert⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
