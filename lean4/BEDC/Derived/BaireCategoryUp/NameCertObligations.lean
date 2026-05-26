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

theorem BaireCategoryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead threadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead →
      Cont R T threadRead →
        PkgSig bundle P pkg →
          UnaryHistory B →
            UnaryHistory M →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory R →
                    UnaryHistory T →
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row denseRead ∨ hsame row threadRead ∨ hsame row M)
                          (fun row : BHist => UnaryHistory row)
                          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
                          hsame ∧
                        baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                          [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro denseRoute threadRoute packageP _BUnary metricUnary denseUnary openUnary
    refinementUnary threadUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementUnary threadUnary threadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row denseRead ∨ hsame row threadRead ∨ hsame row M)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denseRead (Or.inl (hsame_refl denseRead))
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
        | inl sameDense =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameDense)
        | inr rest =>
            cases rest with
            | inl sameThread =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameThread))
            | inr sameMetric =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameMetric))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameDense =>
          exact unary_transport denseReadUnary (hsame_symm sameDense)
      | inr rest =>
          cases rest with
          | inl sameThread =>
              exact unary_transport threadReadUnary (hsame_symm sameThread)
          | inr sameMetric =>
              exact unary_transport metricUnary (hsame_symm sameMetric)
    ledger_sound := by
      intro _row _source
      exact Or.inl packageP
  }
  exact ⟨cert, rfl⟩

end BEDC.Derived.BaireCategoryUp
