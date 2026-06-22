import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def CauchyTailThresholdNormalizerClassifier
    (T U : CauchyTailThresholdNormalizerUp) : Prop :=
  ∃ S M Theta W0 W1 D R A E H C P L N
    S' M' Theta' W0' W1' D' R' A' E' H' C' P' L' N' : BHist,
    cauchyTailThresholdNormalizerFields T =
        [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] ∧
      cauchyTailThresholdNormalizerFields U =
        [S', M', Theta', W0', W1', D', R', A', E', H', C', P', L', N'] ∧
        hsame Theta Theta' ∧ hsame W0 W0' ∧ hsame W1 W1' ∧
          Cont S M Theta ∧ Cont S' M' Theta'

theorem CauchyTailThresholdNormalizerClassifier_threshold_window_routes
    {T U : CauchyTailThresholdNormalizerUp} :
    CauchyTailThresholdNormalizerClassifier T U →
      ∃ S M Theta W0 W1 S' M' Theta' W0' W1' : BHist,
        List.Mem Theta (cauchyTailThresholdNormalizerFields T) ∧
          List.Mem W0 (cauchyTailThresholdNormalizerFields T) ∧
            List.Mem W1 (cauchyTailThresholdNormalizerFields T) ∧
              List.Mem Theta' (cauchyTailThresholdNormalizerFields U) ∧
                List.Mem W0' (cauchyTailThresholdNormalizerFields U) ∧
                  List.Mem W1' (cauchyTailThresholdNormalizerFields U) ∧
                    hsame Theta Theta' ∧ hsame W0 W0' ∧ hsame W1 W1' ∧
                      Cont S M Theta ∧ Cont S' M' Theta' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro classified
  rcases classified with
    ⟨S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N,
      S', M', Theta', W0', W1', D', R', A', E', H', C', P', L', N',
      fieldsT, fieldsU, thresholdSame, leftWindowSame, rightWindowSame,
      sourceRoute, targetRoute⟩
  rw [fieldsT, fieldsU]
  exact
    ⟨S, M, Theta, W0, W1, S', M', Theta', W0', W1',
      List.Mem.tail S (List.Mem.tail M (List.Mem.head _)),
      List.Mem.tail S (List.Mem.tail M (List.Mem.tail Theta (List.Mem.head _))),
      List.Mem.tail S
        (List.Mem.tail M
          (List.Mem.tail Theta (List.Mem.tail W0 (List.Mem.head _)))),
      List.Mem.tail S' (List.Mem.tail M' (List.Mem.head _)),
      List.Mem.tail S' (List.Mem.tail M' (List.Mem.tail Theta' (List.Mem.head _))),
      List.Mem.tail S'
        (List.Mem.tail M'
          (List.Mem.tail Theta' (List.Mem.tail W0' (List.Mem.head _)))),
      thresholdSame, leftWindowSame, rightWindowSame, sourceRoute, targetRoute⟩

theorem CauchyTailThresholdNormalizerSharedThresholdUniqueness [AskSetup]
    [PackageSetup]
    {T U : CauchyTailThresholdNormalizerUp}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailThresholdNormalizerClassifier T U →
      (∃ terminalRead : BHist, PkgSig bundle terminalRead pkg) →
        ∃ Theta Theta' : BHist,
          List.Mem Theta (cauchyTailThresholdNormalizerFields T) ∧
            List.Mem Theta' (cauchyTailThresholdNormalizerFields U) ∧
              hsame Theta Theta' ∧
                SemanticNameCert
                    (fun row : BHist => hsame row Theta ∨ hsame row Theta')
                    (fun row : BHist => hsame row Theta ∨ hsame row Theta')
                    (fun row : BHist =>
                      (hsame row Theta ∨ hsame row Theta') ∧
                        ∃ terminalRead : BHist, PkgSig bundle terminalRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame
  intro classified terminalPkg
  rcases classified with
    ⟨S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N,
      S', M', Theta', W0', W1', D', R', A', E', H', C', P', L', N',
      fieldsT, fieldsU, thresholdSame, _leftWindowSame, _rightWindowSame,
      _sourceRoute, _targetRoute⟩
  have thetaMemT : List.Mem Theta (cauchyTailThresholdNormalizerFields T) := by
    rw [fieldsT]
    exact List.Mem.tail S (List.Mem.tail M (List.Mem.head _))
  have thetaMemU : List.Mem Theta' (cauchyTailThresholdNormalizerFields U) := by
    rw [fieldsU]
    exact List.Mem.tail S' (List.Mem.tail M' (List.Mem.head _))
  have sourceTheta :
      (fun row : BHist => hsame row Theta ∨ hsame row Theta') Theta := by
    exact Or.inl (hsame_refl Theta)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row Theta ∨ hsame row Theta')
          (fun row : BHist => hsame row Theta ∨ hsame row Theta')
          (fun row : BHist =>
            (hsame row Theta ∨ hsame row Theta') ∧
              ∃ terminalRead : BHist, PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Theta sourceTheta
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
        | inr sameTheta' =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameTheta')
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨source, terminalPkg⟩
  }
  exact ⟨Theta, Theta', thetaMemT, thetaMemU, thresholdSame, cert⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
