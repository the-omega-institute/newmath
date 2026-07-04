import BEDC.Derived.ContinuationTerminationUp.NameCertObligations
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContinuationTerminationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationTerminationCarrier_nonescape [AskSetup] [PackageSetup]
    {s t tau u b h p n terminalRead behaviorRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory s → UnaryHistory t → UnaryHistory tau → UnaryHistory u →
      UnaryHistory b → UnaryHistory h → UnaryHistory p → UnaryHistory n →
        Cont t tau terminalRead → Cont u b behaviorRead →
          Cont terminalRead behaviorRead publicRead →
            PkgSig bundle p pkg → PkgSig bundle n pkg →
              SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row s ∨ hsame row t ∨ hsame row tau ∨ hsame row u ∨
                    hsame row b ∨ hsame row h ∨ hsame row p ∨ hsame row n ∨
                      hsame row terminalRead ∨ hsame row behaviorRead ∨
                        hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont t tau terminalRead ∧ Cont u b behaviorRead ∧
                    Cont terminalRead behaviorRead publicRead ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle n pkg)
                hsame ∧
                UnaryHistory terminalRead ∧ UnaryHistory behaviorRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary tUnary tauUnary uUnary bUnary hUnary pUnary nUnary terminalRoute
    behaviorRoute publicRoute pPkg nPkg
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed tUnary tauUnary terminalRoute
  have behaviorUnary : UnaryHistory behaviorRead :=
    unary_cont_closed uUnary bUnary behaviorRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed terminalUnary behaviorUnary publicRoute
  constructor
  · exact
      {
        core := {
          carrier_inhabited :=
            Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row col same
            exact hsame_symm same
          equiv_trans := by
            intro row col target sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row col same source
            exact
              ⟨hsame_trans (hsame_symm same) source.left,
                unary_transport source.right same⟩
        }
        pattern_sound := by
          intro row source
          exact Or.inr
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
          intro row source
          exact
            ⟨source.right, terminalRoute, behaviorRoute, publicRoute, pPkg, nPkg⟩
      }
  · exact ⟨terminalUnary, behaviorUnary, publicUnary⟩

theorem ContinuationTerminationCarrier_nonescape_namecert_surface [AskSetup] [PackageSetup]
    {s t tau u b h p n terminalRead behaviorRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory s → UnaryHistory t → UnaryHistory tau → UnaryHistory u →
      UnaryHistory b → UnaryHistory h → UnaryHistory p → UnaryHistory n →
        Cont t tau terminalRead → Cont u b behaviorRead →
          Cont terminalRead behaviorRead publicRead →
            PkgSig bundle p pkg → PkgSig bundle n pkg →
              SemanticNameCert
                  (ContinuationTerminationObligationRowSpec s t tau u b h p n)
                  (ContinuationTerminationObligationRowSpec s t tau u b h p n)
                  (ContinuationTerminationObligationRowSpec s t tau u b h p n)
                  hsame ∧
                ContinuationTerminationObligationRowSpec s t tau u b h p n s ∧
                  ContinuationTerminationObligationRowSpec s t tau u b h p n t ∧
                    ContinuationTerminationObligationRowSpec s t tau u b h p n tau ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row s ∨ hsame row t ∨ hsame row tau ∨ hsame row u ∨
                            hsame row b ∨ hsame row h ∨ hsame row p ∨ hsame row n ∨
                              hsame row terminalRead ∨ hsame row behaviorRead ∨
                                hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont t tau terminalRead ∧
                            Cont u b behaviorRead ∧
                              Cont terminalRead behaviorRead publicRead ∧
                                PkgSig bundle p pkg ∧ PkgSig bundle n pkg)
                        hsame ∧
                        UnaryHistory terminalRead ∧ UnaryHistory behaviorRead ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro sUnary tUnary tauUnary uUnary bUnary hUnary pUnary nUnary terminalRoute
    behaviorRoute publicRoute pPkg nPkg
  obtain ⟨obligationCert, sRow, tRow, tauRow⟩ :=
    ContinuationTerminationCarrier_namecert_obligations s t tau u b h p n
  obtain ⟨nonescapeCert, terminalUnary, behaviorUnary, publicUnary⟩ :=
    ContinuationTerminationCarrier_nonescape
      (s := s) (t := t) (tau := tau) (u := u) (b := b) (h := h) (p := p)
      (n := n) (terminalRead := terminalRead) (behaviorRead := behaviorRead)
      (publicRead := publicRead) (bundle := bundle) (pkg := pkg)
      sUnary tUnary tauUnary uUnary bUnary hUnary pUnary nUnary terminalRoute
      behaviorRoute publicRoute pPkg nPkg
  exact
    ⟨obligationCert, sRow, tRow, tauRow, nonescapeCert, terminalUnary, behaviorUnary,
      publicUnary⟩

end BEDC.Derived.ContinuationTerminationUp
