import BEDC.Derived.NatUp.AddSourceSpineForwardLink

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatAddIntUnaryChainOrphanLink {left right sum spine positive negative balance : BHist} :
    UnaryHistory left →
      UnaryHistory right →
        Cont left right sum →
          Cont sum BHist.Empty spine →
            UnaryHistory positive →
              UnaryHistory negative →
                hsame positive left →
                  hsame negative right →
                    Cont positive negative balance →
                      UnaryHistory sum ∧ UnaryHistory spine ∧ UnaryHistory balance ∧
                        hsame sum spine ∧ Cont left right sum ∧
                          Cont positive negative balance := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro leftUnary rightUnary leftRightSum sumEmptySpine positiveUnary negativeUnary
    _samePositive _sameNegative positiveNegativeBalance
  have addSpine :
      UnaryHistory sum ∧ UnaryHistory spine ∧ Cont left right sum ∧
        Cont sum BHist.Empty spine ∧ hsame sum spine :=
    NatAddSourceSpine_forward_link leftUnary rightUnary leftRightSum sumEmptySpine
  have balanceUnary : UnaryHistory balance :=
    unary_cont_closed positiveUnary negativeUnary positiveNegativeBalance
  exact
    ⟨addSpine.left, addSpine.right.left, balanceUnary, addSpine.right.right.right.right,
      addSpine.right.right.left, positiveNegativeBalance⟩

end BEDC.Derived.NatUp
