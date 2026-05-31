import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteMetricRootObligation [AskSetup] [PackageSetup]
    {metric complete stream readback ledger transport route completionRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory stream →
          UnaryHistory readback →
            UnaryHistory ledger →
              UnaryHistory transport →
                Cont metric stream route →
                  Cont complete stream completionRead →
                    Cont ledger transport route →
                      Cont route readback rootRead →
                        PkgSig bundle rootRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row metric ∨ hsame row complete ∨ hsame row stream ∨
                                  hsame row ledger ∨ hsame row rootRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle rootRead pkg ∧
                                  Cont complete stream completionRead)
                              hsame ∧
                            UnaryHistory completionRead ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _metricUnary completeUnary streamUnary readbackUnary ledgerUnary transportUnary
    _metricStreamRoute completeStreamCompletion ledgerTransportRoute routeReadbackRoot rootPkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary readbackUnary routeReadbackRoot
  have sourceRoot :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row stream ∨
              hsame row ledger ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle rootRead pkg ∧
              Cont complete stream completionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRoot
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
      exact ⟨source.right, rootPkg, completeStreamCompletion⟩
  }
  exact ⟨cert, completionUnary, rootUnary⟩

end BEDC.Derived.PolishspaceUp
