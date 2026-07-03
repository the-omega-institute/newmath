import BEDC.Derived.RealPolynomialUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealPolynomialUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPolynomialNameCertObligations [AskSetup] [PackageSetup]
    {A X Q S G W D E M evalRead mapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory X ->
        UnaryHistory Q ->
          UnaryHistory S ->
            UnaryHistory G ->
              UnaryHistory W ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    UnaryHistory M ->
                      Cont A X evalRead ->
                        Cont evalRead Q mapRead ->
                          Cont mapRead M E ->
                            PkgSig bundle E pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row E ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row A ∨ hsame row X ∨ hsame row Q ∨
                                      hsame row S ∨ hsame row G ∨ hsame row W ∨
                                        hsame row D ∨ hsame row E ∨ hsame row M)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont A X evalRead ∧
                                      Cont evalRead Q mapRead ∧ Cont mapRead M E ∧
                                        PkgSig bundle E pkg)
                                  hsame ∧
                                UnaryHistory evalRead ∧ UnaryHistory mapRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro aUnary xUnary qUnary _sUnary _gUnary _wUnary _dUnary eUnary mUnary evalRoute
    mapRoute handoffRoute evalPkg
  have evalUnary : UnaryHistory evalRead :=
    unary_cont_closed aUnary xUnary evalRoute
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed evalUnary qUnary mapRoute
  have terminalUnary : UnaryHistory E :=
    unary_cont_closed mapUnary mUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row X ∨ hsame row Q ∨ hsame row S ∨ hsame row G ∨
              hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row M)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A X evalRead ∧ Cont evalRead Q mapRead ∧
              Cont mapRead M E ∧ PkgSig bundle E pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨E, hsame_refl E, terminalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, evalRoute, mapRoute, handoffRoute, evalPkg⟩
  }
  exact ⟨cert, evalUnary, mapUnary⟩

end BEDC.Derived.RealPolynomialUp
