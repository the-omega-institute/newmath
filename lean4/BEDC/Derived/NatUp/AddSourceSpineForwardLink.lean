import BEDC.Derived.NatUp

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatAddSourceSpine_forward_link {left right sum spine : BHist} :
    UnaryHistory left →
      UnaryHistory right →
        Cont left right sum →
          Cont sum BHist.Empty spine →
            UnaryHistory sum ∧ UnaryHistory spine ∧ Cont left right sum ∧
              Cont sum BHist.Empty spine ∧ hsame sum spine := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro leftUnary rightUnary leftRightSum sumEmptySpine
  have sumUnary : UnaryHistory sum :=
    unary_cont_closed leftUnary rightUnary leftRightSum
  have spineUnary : UnaryHistory spine :=
    unary_cont_closed sumUnary unary_empty sumEmptySpine
  have sameSumSpine : hsame sum spine :=
    hsame_symm (cont_deterministic sumEmptySpine (cont_right_unit sum))
  exact ⟨sumUnary, spineUnary, leftRightSum, sumEmptySpine, sameSumSpine⟩

end BEDC.Derived.NatUp
