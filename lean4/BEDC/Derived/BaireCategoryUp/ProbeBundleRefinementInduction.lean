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

theorem BaireCategoryCarrier_probe_bundle_refinement_induction [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead refinedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead ->
      Cont denseRead R refinedRead ->
        Cont refinedRead H replayRead ->
          PkgSig bundle P pkg ->
            UnaryHistory D ->
              UnaryHistory O ->
                UnaryHistory R ->
                  UnaryHistory H ->
                    SemanticNameCert
                        (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row H ∨
                            hsame row replayRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                            Cont refinedRead H replayRead)
                        hsame ∧
                      UnaryHistory denseRead ∧ UnaryHistory refinedRead ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro denseRoute refinedRoute replayRoute packageP denseUnary openUnary refinementUnary
    handoffUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed denseReadUnary refinementUnary refinedRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed refinedReadUnary handoffUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row H ∨
              hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont refinedRead H replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packageP, replayRoute⟩
  }
  exact ⟨cert, denseReadUnary, refinedReadUnary, replayReadUnary⟩

end BEDC.Derived.BaireCategoryUp
