import BEDC.Derived.FableMachineBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FableMachineBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FableMachineBoundarySelectorNonescape
    {history emptyBoundary ledger selector witness clock transport route provenance name selectorRead
      witnessRead : BHist} :
    Cont ledger selector selectorRead ->
      Cont selectorRead witness witnessRead ->
        UnaryHistory history -> UnaryHistory emptyBoundary -> UnaryHistory ledger ->
          UnaryHistory selector -> UnaryHistory witness -> UnaryHistory clock ->
            UnaryHistory transport -> UnaryHistory route -> UnaryHistory provenance ->
              UnaryHistory name ->
                SemanticNameCert
                  (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row history ∨ hsame row emptyBoundary ∨ hsame row ledger ∨
                      hsame row selector ∨ hsame row witness ∨ hsame row clock ∨
                        hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                          hsame row name ∨ hsame row selectorRead ∨ hsame row witnessRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont ledger selector selectorRead ∧
                      Cont selectorRead witness witnessRead)
                  hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro selectorRoute witnessRoute _historyUnary _emptyUnary ledgerUnary selectorUnary
    witnessUnary _clockUnary _transportUnary _routeUnary _provenanceUnary _nameUnary
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed ledgerUnary selectorUnary selectorRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed selectorReadUnary witnessUnary witnessRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row history ∨ hsame row emptyBoundary ∨ hsame row ledger ∨
            hsame row selector ∨ hsame row witness ∨ hsame row clock ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row name ∨ hsame row selectorRead ∨ hsame row witnessRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont ledger selector selectorRead ∧
            Cont selectorRead witness witnessRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessReadUnary⟩
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
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, selectorRoute, witnessRoute⟩
  }
  exact ⟨cert, selectorReadUnary, witnessReadUnary⟩

end BEDC.Derived.FableMachineBoundaryUp
