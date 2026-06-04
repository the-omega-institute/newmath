import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceSelectionSurface_namecert_window [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N selectionWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg →
      Cont M Q selectionWindow →
        PkgSig bundle selectionWindow pkg →
          SemanticNameCert
              (fun row : BHist => hsame row selectionWindow ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row W ∨ hsame row H ∨
                  hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row selectionWindow)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M Q selectionWindow ∧
                  PkgSig bundle selectionWindow pkg)
              hsame ∧
            UnaryHistory selectionWindow := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectionRoute selectionPkg
  obtain ⟨_sourceUnary, modulusUnary, selectorUnary, _fastUnary, _regularUnary, _readbackUnary,
    _sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg, _localNamePkg⟩ := carrier
  have selectionUnary : UnaryHistory selectionWindow :=
    unary_cont_closed modulusUnary selectorUnary selectionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectionWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row W ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row selectionWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q selectionWindow ∧
              PkgSig bundle selectionWindow pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro selectionWindow ⟨hsame_refl selectionWindow, selectionUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, selectionRoute, selectionPkg⟩
  }
  exact ⟨cert, selectionUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
