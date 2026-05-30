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

theorem BaireCategoryCarrier_refinement_choice_free [AskSetup] [PackageSetup]
    {_B M D O R T _H _C P _N denseRead refinedRead threadRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D O denseRead →
      Cont denseRead R refinedRead →
        Cont refinedRead T threadRead →
          Cont threadRead M terminalRead →
            PkgSig bundle P pkg →
              PkgSig bundle terminalRead pkg →
                UnaryHistory D →
                  UnaryHistory O →
                    UnaryHistory R →
                      UnaryHistory T →
                        UnaryHistory M →
                          SemanticNameCert
                              (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨
                                  hsame row M ∨ hsame row terminalRead)
                              (fun _row : BHist =>
                                PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg)
                              hsame ∧
                            UnaryHistory denseRead ∧ UnaryHistory refinedRead ∧
                              UnaryHistory threadRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro denseRoute refinedRoute threadRoute terminalRoute packageP terminalPkg denseUnary
    openUnary refinementUnary threadUnary metricUnary
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed denseReadUnary refinementUnary refinedRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinedReadUnary threadUnary threadRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed threadReadUnary metricUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨ hsame row M ∨
              hsame row terminalRead)
          (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalReadUnary⟩
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
      intro _row _source
      exact ⟨packageP, terminalPkg⟩
  }
  exact ⟨cert, denseReadUnary, refinedReadUnary, threadReadUnary, terminalReadUnary⟩

end BEDC.Derived.BaireCategoryUp
