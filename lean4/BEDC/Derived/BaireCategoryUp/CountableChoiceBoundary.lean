import BEDC.Derived.BaireCategoryUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_countable_choice_boundary [AskSetup] [PackageSetup]
    {B M D O R T H C P N terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory M →
        Cont T M terminal →
          PkgSig bundle terminal pkg →
            PkgSig bundle P pkg →
              baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                  [B, M, D, O, R, T, H, C, P, N] ∧
                SemanticNameCert
                    (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row M ∨ hsame row D ∨ hsame row O ∨
                        hsame row R ∨ hsame row T ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row terminal)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle terminal pkg ∧
                        (hsame row T ∨ hsame row M ∨ hsame row terminal))
                    hsame ∧
                  UnaryHistory terminal := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro threadUnary metricUnary threadMetricTerminal terminalPkg packageP
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed threadUnary metricUnary threadMetricTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row M ∨ hsame row D ∨ hsame row O ∨ hsame row R ∨
              hsame row T ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row terminal)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle terminal pkg ∧
              (hsame row T ∨ hsame row M ∨ hsame row terminal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal ⟨hsame_refl terminal, terminalUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨packageP, terminalPkg, Or.inr (Or.inr source.left)⟩
  }
  exact ⟨rfl, cert, terminalUnary⟩

end BEDC.Derived.BaireCategoryUp
