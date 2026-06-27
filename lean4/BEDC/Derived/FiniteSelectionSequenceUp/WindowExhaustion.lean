import BEDC.Derived.FiniteSelectionSequenceUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteSelectionSequenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FiniteSelectionSequenceWindowExhaustion
    {W D R T C P N thresholdRead readbackRead sealRead : BHist} :
    UnaryHistory W ->
      UnaryHistory D ->
        UnaryHistory R ->
          UnaryHistory C ->
            Cont W D thresholdRead ->
              Cont thresholdRead R readbackRead ->
                Cont readbackRead C sealRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row T ∨
                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row thresholdRead ∨ hsame row readbackRead ∨
                              hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W D thresholdRead ∧
                          Cont thresholdRead R readbackRead ∧ Cont readbackRead C sealRead)
                      hsame ∧
                    UnaryHistory thresholdRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro wUnary dUnary rUnary cUnary thresholdRoute readbackRoute sealRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed wUnary dUnary thresholdRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed thresholdUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary cUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row T ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row thresholdRead ∨
                hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D thresholdRead ∧
              Cont thresholdRead R readbackRead ∧ Cont readbackRead C sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdRoute, readbackRoute, sealRoute⟩
  }
  exact ⟨cert, thresholdUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.FiniteSelectionSequenceUp
