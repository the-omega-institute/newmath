import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.OrdinalAnalysisUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem OrdinalAnalysisCarrier_namecert_obligations
    {A B C U L H R P N budgetRead traceRead consumerRead : BHist} :
    UnaryHistory A → UnaryHistory B → UnaryHistory C → UnaryHistory U →
      UnaryHistory L → UnaryHistory H → UnaryHistory R → UnaryHistory P →
        UnaryHistory N → Cont A B budgetRead → Cont budgetRead C traceRead →
          Cont traceRead U consumerRead → hsame H R →
            SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row C ∨ hsame row U ∨
                  hsame row L ∨ hsame row H ∨ hsame row R ∨ hsame row P ∨
                    hsame row N ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont A B budgetRead ∧ Cont budgetRead C traceRead ∧
                  Cont traceRead U consumerRead ∧ hsame H R)
              hsame ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro notationUnary budgetUnary traceUnary consumerUnary _ledgerUnary _transportUnary
    _replayUnary _provenanceUnary _nameUnary budgetRoute traceRoute consumerRoute sameHR
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed notationUnary budgetUnary budgetRoute
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed budgetReadUnary traceUnary traceRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed traceReadUnary consumerUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row C ∨ hsame row U ∨
              hsame row L ∨ hsame row H ∨ hsame row R ∨ hsame row P ∨
                hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A B budgetRead ∧ Cont budgetRead C traceRead ∧
              Cont traceRead U consumerRead ∧ hsame H R)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, budgetRoute, traceRoute, consumerRoute, sameHR⟩
  }
  exact ⟨cert, consumerReadUnary⟩

end BEDC.Derived.OrdinalAnalysisUp
