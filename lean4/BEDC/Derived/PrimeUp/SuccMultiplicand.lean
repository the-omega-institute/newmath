import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_succ_multiplicand_append_multiplier_total {d q n : BHist} :
    NatMul d q n -> ∃ r : BHist, UnaryHistory r ∧ Cont n q r ∧
      NatMul (BHist.e1 d) q r := by
  intro mul
  induction mul with
  | zero hd =>
      exact
        Exists.intro BHist.Empty
          (And.intro unary_empty
            (And.intro (cont_intro rfl) (NatMul.zero (unary_e1_closed hd))))
  | succ previous step ih =>
      rename_i qTail nPrev nNext
      cases ih with
      | intro r rData =>
          have dUnary : UnaryHistory d := NatMul_left_unary previous
          have qUnary : UnaryHistory _ := NatMul_right_unary previous
          have displayed : Cont nNext (BHist.e1 qTail) (append r (BHist.e1 d)) := by
            cases step
            cases rData.right.left
            exact
              cont_intro
                (congrArg BHist.e1
                  ((append_assoc nPrev qTail d).trans
                    ((congrArg (fun x => append nPrev x)
                      (unary_append_comm qUnary dUnary)).trans
                        (append_assoc nPrev d qTail).symm)))
          exact
            Exists.intro (append r (BHist.e1 d))
              (And.intro (unary_append_closed rData.left (unary_e1_closed dUnary))
                (And.intro displayed (NatMul.succ rData.right.right (cont_intro rfl))))

end BEDC.Derived.PrimeUp
