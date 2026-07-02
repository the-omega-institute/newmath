import BEDC.Derived.FiniteWindowRealSeparationUp.NameCertSurface

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparation_terminal_readback_exclusion [AskSetup] [PackageSetup]
    {W D S R H C P N toleranceRead readbackRead separationRead namedRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W → UnaryHistory D → UnaryHistory S → UnaryHistory R →
      UnaryHistory N → UnaryHistory P → Cont W D toleranceRead →
        Cont toleranceRead S readbackRead → Cont readbackRead R separationRead →
          Cont separationRead N namedRead → Cont namedRead P terminalRead →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row toleranceRead ∨ hsame row readbackRead ∨
                          hsame row separationRead ∨ hsame row namedRead ∨
                            hsame row terminalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W D toleranceRead ∧
                      Cont toleranceRead S readbackRead ∧
                        Cont readbackRead R separationRead ∧
                          Cont separationRead N namedRead ∧ Cont namedRead P terminalRead ∧
                            PkgSig bundle P pkg)
                  hsame ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryS unaryR unaryN unaryP toleranceRoute readbackRoute
    separationRoute namedRoute terminalRoute pkgP
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed readbackUnary unaryR separationRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separationUnary unaryN namedRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed namedUnary unaryP terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row toleranceRead ∨
                hsame row readbackRead ∨ hsame row separationRead ∨ hsame row namedRead ∨
                  hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont readbackRead R separationRead ∧
                Cont separationRead N namedRead ∧ Cont namedRead P terminalRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, toleranceRoute, readbackRoute, separationRoute, namedRoute,
          terminalRoute, pkgP⟩
  }
  exact ⟨cert, terminalUnary⟩

end BEDC.Derived.FiniteWindowRealSeparationUp
