import BEDC.Derived.CauchyTailThresholdNormalizerUp.Classifier
import BEDC.Derived.CauchyTailThresholdNormalizerUp.TailWindowInduction
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerUniformThresholdInduction [AskSetup] [PackageSetup]
    {T U : CauchyTailThresholdNormalizerUp}
    {S M Theta W0 W1 D R A E H C P L N terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyTailThresholdNormalizerFields T = [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] ->
      CauchyTailThresholdNormalizerClassifier T U ->
        UnaryHistory Theta ->
          UnaryHistory W0 ->
            UnaryHistory D ->
              UnaryHistory A ->
                UnaryHistory C ->
                  Cont Theta W0 W1 ->
                    Cont W1 D R ->
                      Cont R A E ->
                        Cont E C terminalRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row Theta ∨ hsame row W1 ∨ hsame row R ∨
                                    hsame row E ∨ hsame row terminalRead)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row M ∨ hsame row Theta ∨
                                    hsame row W0 ∨ hsame row W1 ∨ hsame row D ∨
                                      hsame row R ∨ hsame row A ∨ hsame row E ∨
                                        hsame row terminalRead)
                                (fun row : BHist =>
                                  (hsame row Theta ∨ hsame row W1 ∨ hsame row R ∨
                                      hsame row E ∨ hsame row terminalRead) ∧
                                    UnaryHistory terminalRead ∧ PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fields classified thetaUnary w0Unary dUnary aUnary cUnary thresholdRoute
    readbackRoute agreementRoute terminalRoute pkgSig
  have tailData :=
    CauchyTailThresholdNormalizerTailWindowInduction (T := T) (S := S) (M := M)
      (Theta := Theta) (W0 := W0) (W1 := W1) (D := D) (R := R) (A := A)
      (E := E) (H := H) (C := C) (P := P) (L := L) (N := N)
      (terminalRead := terminalRead) fields thetaUnary w0Unary dUnary aUnary cUnary
      thresholdRoute readbackRoute agreementRoute terminalRoute
  rcases tailData with
    ⟨_thetaMem, _w0Mem, _w1Mem, _dMem, _rMem, w1Unary, rUnary, eUnary,
      terminalUnary⟩
  have classifierSourceRoute : Cont S M Theta := by
    rcases classified with
      ⟨S', M', Theta', W0', W1', D', R', A', E', H', C', P', L', N',
        S'', M'', Theta'', W0'', W1'', D'', R'', A'', E'', H'', C'', P'', L'', N'',
        fieldsLeft, _fieldsRight, _thetaSame, _w0Same, _w1Same, sourceRoute,
        _targetRoute⟩
    cases Eq.trans fields.symm fieldsLeft
    exact sourceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row Theta ∨ hsame row W1 ∨ hsame row R ∨ hsame row E ∨
              hsame row terminalRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨
              hsame row W1 ∨ hsame row D ∨ hsame row R ∨ hsame row A ∨
                hsame row E ∨ hsame row terminalRead)
          (fun row : BHist =>
            (hsame row Theta ∨ hsame row W1 ∨ hsame row R ∨ hsame row E ∨
                hsame row terminalRead) ∧
              UnaryHistory terminalRead ∧ PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro Theta (Or.inl (hsame_refl Theta))
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
          cases source with
          | inl sameTheta =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTheta)
          | inr rest =>
              cases rest with
              | inl sameW1 =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameW1))
              | inr rest =>
                  cases rest with
                  | inl sameR =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR)))
                  | inr rest =>
                      cases rest with
                      | inl sameE =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameE))))
                      | inr sameTerminal =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (hsame_trans (hsame_symm sameRows) sameTerminal))))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl sameTheta =>
            exact Or.inr (Or.inr (Or.inl sameTheta))
        | inr rest =>
            cases rest with
            | inl sameW1 =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameW1))))
            | inr rest =>
                cases rest with
                | inl sameR =>
                    exact Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameR))))))
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr (Or.inl sameE))))))))
                    | inr sameTerminal =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr (Or.inr sameTerminal))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source, terminalUnary, pkgSig⟩
    }
  exact ⟨cert, terminalUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
