import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicUpTerminalRealSealBoundary [AskSetup] [PackageSetup]
    {Q S R E H C P N terminalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory E ->
        Cont Q S R ->
          Cont R E terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row terminalRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRead pkg)
                  hsame ∧
                UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary eUnary _qsrRoute terminalRoute terminalPkg
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed rUnary eUnary terminalRoute
  have sourceAtTerminal :
      hsame terminalRead terminalRead ∧ UnaryHistory terminalRead :=
    ⟨hsame_refl terminalRead, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row terminalRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceAtTerminal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, terminalPkg⟩
  }
  exact ⟨cert, terminalUnary⟩

end BEDC.Derived.DyadicUp
