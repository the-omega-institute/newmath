import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

inductive AlgebraicExpressionLedgerUp : Type where
  | mk : (e o a u s h c p n : BHist) → AlgebraicExpressionLedgerUp
  deriving DecidableEq

namespace AlgebraicExpressionLedgerUp

def AlgebraicExpressionLedgerCarrier
    (E O A U S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  UnaryHistory E ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory U ∧
    UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N

theorem AlgebraicExpressionLedgerCarrier_namecert_obligations
    {E O A U S H C P N parseRead sealRead : BHist} :
    AlgebraicExpressionLedgerCarrier E O A U S H C P N →
      Cont E O parseRead →
        Cont parseRead C sealRead →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row E ∨ hsame row O ∨ hsame row A ∨ hsame row U ∨
                  hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row sealRead)
              (fun row : BHist =>
                hsame row sealRead ∧ Cont E O parseRead ∧ Cont parseRead C sealRead)
              hsame ∧
            UnaryHistory parseRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier parseRoute sealRoute
  have eUnary : UnaryHistory E := carrier.left
  have oUnary : UnaryHistory O := carrier.right.left
  have cUnary : UnaryHistory C := carrier.right.right.right.right.right.right.left
  have parseUnary : UnaryHistory parseRead :=
    unary_cont_closed eUnary oUnary parseRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed parseUnary cUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row O ∨ hsame row A ∨ hsame row U ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont E O parseRead ∧ Cont parseRead C sealRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, parseRoute, sealRoute⟩
  }
  exact ⟨cert, parseUnary, sealUnary⟩

end AlgebraicExpressionLedgerUp

end BEDC.Derived
