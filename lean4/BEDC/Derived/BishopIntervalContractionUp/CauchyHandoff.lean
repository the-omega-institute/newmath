import BEDC.Derived.BishopIntervalContractionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BishopIntervalContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BishopIntervalContractionCauchyHandoff [AskSetup] [PackageSetup]
    {I F L D W R E H C P N intervalRead windowRead readbackSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I F intervalRead →
      Cont D W windowRead →
        Cont R E readbackSeal →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              bishopIntervalContractionFields
                    (BishopIntervalContractionUp.mk I F L D W R E H C P N) =
                  [I, F, L, D, W, R, E, H, C, P, N] ∧
                SemanticNameCert
                  (fun row : BHist => hsame row readbackSeal)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row F ∨ hsame row L ∨ hsame row D ∨
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row readbackSeal)
                  (fun row : BHist =>
                    Cont I F intervalRead ∧ Cont D W windowRead ∧
                      Cont R E readbackSeal ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg ∧ hsame row readbackSeal)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro intervalRoute windowRoute readbackRoute provenancePkg localNamePkg
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row readbackSeal)
        (fun row : BHist =>
          hsame row I ∨ hsame row F ∨ hsame row L ∨ hsame row D ∨
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row readbackSeal)
        (fun row : BHist =>
          Cont I F intervalRead ∧ Cont D W windowRead ∧ Cont R E readbackSeal ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row readbackSeal)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackSeal (hsame_refl readbackSeal)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr source))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨intervalRoute, windowRoute, readbackRoute, provenancePkg, localNamePkg,
          source⟩
  }
  exact ⟨rfl, cert⟩

theorem BishopIntervalContraction_shrinkage_composition
    (x : BishopIntervalContractionUp) :
    ∃ I F L D W R E H C P N shrinkRoute windowRoute terminalRoute : BHist,
      x = BishopIntervalContractionUp.mk I F L D W R E H C P N ∧
        bishopIntervalContractionFields x = [I, F, L, D, W, R, E, H, C, P, N] ∧
          Cont (append I F) (append L D) shrinkRoute ∧
            Cont shrinkRoute (append W R) windowRoute ∧
              Cont windowRoute E terminalRoute ∧
                hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk I F L D W R E H C P N =>
      exact
        ⟨I, F, L, D, W, R, E, H, C, P, N,
          append (append I F) (append L D),
          append (append (append I F) (append L D)) (append W R),
          append (append (append (append I F) (append L D)) (append W R)) E,
          rfl, rfl, rfl, rfl, rfl, hsame_refl H, hsame_refl C, hsame_refl P,
          hsame_refl N⟩

end BEDC.Derived.BishopIntervalContractionUp
