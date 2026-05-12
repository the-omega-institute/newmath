import BEDC.Derived.PrimeUp
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatDivides_cont_closed {d x y z : BHist} :
    NatDivides d x → NatDivides d y → Cont x y z → NatDivides d z := by
  intro dividesX dividesY continuation
  cases dividesX with
  | intro qx qxData =>
      cases qxData with
      | intro qxUnary qxMul =>
          cases dividesY with
          | intro qy qyData =>
              cases qyData with
              | intro qyUnary qyMul =>
                  exact Exists.intro (append qx qy)
                    (And.intro (unary_append_closed qxUnary qyUnary)
                      (NatMul_append_cont qxMul qyMul continuation))

theorem NatMul_append_multiplier_total {d w n q : BHist} :
    NatMul d w n -> UnaryHistory q ->
      ∃ r : BHist, UnaryHistory r ∧ NatMul d (append w q) r := by
  intro mul qUnary
  have dUnary : UnaryHistory d := NatMul_left_unary mul
  have nUnary : UnaryHistory n := NatMul_result_unary dUnary mul
  have qProduct := NatMul_total dUnary qUnary
  cases qProduct with
  | intro e eData =>
      exact Exists.intro (append n e)
        (And.intro (unary_cont_closed nUnary eData.left (cont_intro rfl))
          (NatMul_append_cont mul eData.right (cont_intro rfl)))

theorem NatDivides_mul_right_closed {d q n : BHist} :
    UnaryHistory d -> UnaryHistory q -> NatMul d q n -> NatDivides q n := by
  intro dUnary qUnary mul
  have qProduct := NatMul_total qUnary dUnary
  cases qProduct with
  | intro m mData =>
      have sameResult : hsame n m := NatMul_comm_hsame dUnary qUnary mul mData.right
      have dividesM : NatDivides q m := Exists.intro d (And.intro dUnary mData.right)
      exact (NatDivides_dividend_hsame_transport dividesM (hsame_symm sameResult)).right

theorem NatPrime_NatMul_factors_not_empty {p d q : BHist} :
    NatPrime p -> UnaryHistory d -> UnaryHistory q -> NatMul d q p ->
      (hsame d BHist.Empty -> False) ∧ (hsame q BHist.Empty -> False) := by
  intro prime dUnary qUnary mul
  constructor
  · intro dEmpty
    have dDividesP : NatDivides d p := Exists.intro q (And.intro qUnary mul)
    exact NatPrime_divisor_empty_absurd prime dDividesP dEmpty
  · intro qEmpty
    have qDividesP : NatDivides q p := NatDivides_mul_right_closed dUnary qUnary mul
    exact NatPrime_divisor_empty_absurd prime qDividesP qEmpty

theorem NatDivides_mul_left_closed {d x q z : BHist} :
    UnaryHistory x -> NatDivides d q -> NatMul x q z -> NatDivides d z := by
  intro xUnary divides mul
  have qUnary : UnaryHistory q := NatDivides_result_unary divides
  have qProduct := NatMul_total qUnary xUnary
  cases qProduct with
  | intro z' zData =>
      have sameProduct : hsame z z' :=
        NatMul_comm_hsame xUnary qUnary mul zData.right
      have qDividesProduct : NatDivides q z' :=
        Exists.intro x (And.intro xUnary zData.right)
      have qDividesZ : NatDivides q z :=
        (NatDivides_dividend_hsame_transport qDividesProduct (hsame_symm sameProduct)).right
      exact NatDivides_transitive divides qDividesZ

private theorem NatDivides_product_closed_unary_hsame_aux {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      BEDC.FKernel.ExternalBinary.bwordLength h =
        BEDC.FKernel.ExternalBinary.bwordLength k -> hsame h k := by
  intro unaryH
  induction h generalizing k with
  | Empty =>
      intro unaryK lengthEq
      cases k with
      | Empty =>
          rfl
      | e0 k =>
          cases unaryK
      | e1 k =>
          cases lengthEq
  | e0 h _ih =>
      cases unaryH
  | e1 h ih =>
      intro unaryK lengthEq
      cases k with
      | Empty =>
          cases lengthEq
      | e0 k =>
          cases unaryK
      | e1 k =>
          exact hsame_e1_congr (ih unaryH unaryK (Nat.succ.inj lengthEq))

private theorem NatDivides_product_closed_nat_mul_assoc_aux (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

theorem NatDivides_product_closed {d e x y p z : BHist} :
    UnaryHistory d -> UnaryHistory e -> UnaryHistory x -> UnaryHistory y ->
      NatDivides d x -> NatDivides e y -> NatMul d e p -> NatMul x y z ->
        NatDivides p z := by
  intro dUnary eUnary xUnary _yUnary dividesX dividesY productDE productXY
  cases dividesX with
  | intro q qData =>
      cases dividesY with
      | intro r rData =>
          have pUnary : UnaryHistory p := NatMul_result_unary dUnary productDE
          have quotientProduct := NatMul_total qData.left rData.left
          cases quotientProduct with
          | intro s sData =>
              have displayedProduct := NatMul_total pUnary sData.left
              cases displayedProduct with
              | intro displayed displayedData =>
                  have zUnary : UnaryHistory z := NatMul_result_unary xUnary productXY
                  have sameDisplayed : hsame z displayed := by
                    have lengthEq :
                        BEDC.FKernel.ExternalBinary.bwordLength z =
                          BEDC.FKernel.ExternalBinary.bwordLength displayed := by
                      calc
                        BEDC.FKernel.ExternalBinary.bwordLength z =
                            BEDC.FKernel.ExternalBinary.bwordLength x *
                              BEDC.FKernel.ExternalBinary.bwordLength y :=
                          NatMul_bwordLength productXY
                        _ =
                            (BEDC.FKernel.ExternalBinary.bwordLength d *
                                BEDC.FKernel.ExternalBinary.bwordLength q) *
                              (BEDC.FKernel.ExternalBinary.bwordLength e *
                                BEDC.FKernel.ExternalBinary.bwordLength r) :=
                          congrArg
                            (fun n =>
                              n * BEDC.FKernel.ExternalBinary.bwordLength y)
                            (NatMul_bwordLength qData.right) |>.trans
                            (congrArg
                              (fun n =>
                                (BEDC.FKernel.ExternalBinary.bwordLength d *
                                  BEDC.FKernel.ExternalBinary.bwordLength q) * n)
                              (NatMul_bwordLength rData.right))
                        _ =
                            (BEDC.FKernel.ExternalBinary.bwordLength d *
                                BEDC.FKernel.ExternalBinary.bwordLength e) *
                              (BEDC.FKernel.ExternalBinary.bwordLength q *
                                BEDC.FKernel.ExternalBinary.bwordLength r) := by
                          calc
                            (BEDC.FKernel.ExternalBinary.bwordLength d *
                                BEDC.FKernel.ExternalBinary.bwordLength q) *
                              (BEDC.FKernel.ExternalBinary.bwordLength e *
                                BEDC.FKernel.ExternalBinary.bwordLength r) =
                                BEDC.FKernel.ExternalBinary.bwordLength d *
                                  (BEDC.FKernel.ExternalBinary.bwordLength q *
                                    (BEDC.FKernel.ExternalBinary.bwordLength e *
                                      BEDC.FKernel.ExternalBinary.bwordLength r)) :=
                              NatDivides_product_closed_nat_mul_assoc_aux
                                (BEDC.FKernel.ExternalBinary.bwordLength d)
                                (BEDC.FKernel.ExternalBinary.bwordLength q)
                                (BEDC.FKernel.ExternalBinary.bwordLength e *
                                  BEDC.FKernel.ExternalBinary.bwordLength r)
                            _ =
                                BEDC.FKernel.ExternalBinary.bwordLength d *
                                  ((BEDC.FKernel.ExternalBinary.bwordLength q *
                                      BEDC.FKernel.ExternalBinary.bwordLength e) *
                                    BEDC.FKernel.ExternalBinary.bwordLength r) :=
                              congrArg
                                (fun n => BEDC.FKernel.ExternalBinary.bwordLength d * n)
                                (NatDivides_product_closed_nat_mul_assoc_aux
                                  (BEDC.FKernel.ExternalBinary.bwordLength q)
                                  (BEDC.FKernel.ExternalBinary.bwordLength e)
                                  (BEDC.FKernel.ExternalBinary.bwordLength r)).symm
                            _ =
                                BEDC.FKernel.ExternalBinary.bwordLength d *
                                  ((BEDC.FKernel.ExternalBinary.bwordLength e *
                                      BEDC.FKernel.ExternalBinary.bwordLength q) *
                                    BEDC.FKernel.ExternalBinary.bwordLength r) :=
                              congrArg
                                (fun n =>
                                  BEDC.FKernel.ExternalBinary.bwordLength d *
                                    (n * BEDC.FKernel.ExternalBinary.bwordLength r))
                                (Nat.mul_comm
                                  (BEDC.FKernel.ExternalBinary.bwordLength q)
                                  (BEDC.FKernel.ExternalBinary.bwordLength e))
                            _ =
                                BEDC.FKernel.ExternalBinary.bwordLength d *
                                  (BEDC.FKernel.ExternalBinary.bwordLength e *
                                    (BEDC.FKernel.ExternalBinary.bwordLength q *
                                      BEDC.FKernel.ExternalBinary.bwordLength r)) :=
                              congrArg
                                (fun n => BEDC.FKernel.ExternalBinary.bwordLength d * n)
                                (NatDivides_product_closed_nat_mul_assoc_aux
                                  (BEDC.FKernel.ExternalBinary.bwordLength e)
                                  (BEDC.FKernel.ExternalBinary.bwordLength q)
                                  (BEDC.FKernel.ExternalBinary.bwordLength r))
                            _ =
                                (BEDC.FKernel.ExternalBinary.bwordLength d *
                                  BEDC.FKernel.ExternalBinary.bwordLength e) *
                                    (BEDC.FKernel.ExternalBinary.bwordLength q *
                                      BEDC.FKernel.ExternalBinary.bwordLength r) :=
                              (NatDivides_product_closed_nat_mul_assoc_aux
                                (BEDC.FKernel.ExternalBinary.bwordLength d)
                                (BEDC.FKernel.ExternalBinary.bwordLength e)
                                (BEDC.FKernel.ExternalBinary.bwordLength q *
                                  BEDC.FKernel.ExternalBinary.bwordLength r)).symm
                        _ =
                            BEDC.FKernel.ExternalBinary.bwordLength p *
                              BEDC.FKernel.ExternalBinary.bwordLength s :=
                          congrArg
                            (fun n =>
                              n *
                                (BEDC.FKernel.ExternalBinary.bwordLength q *
                                  BEDC.FKernel.ExternalBinary.bwordLength r))
                            (NatMul_bwordLength productDE).symm |>.trans
                            (congrArg
                              (fun n => BEDC.FKernel.ExternalBinary.bwordLength p * n)
                              (NatMul_bwordLength sData.right).symm)
                        _ = BEDC.FKernel.ExternalBinary.bwordLength displayed :=
                          (NatMul_bwordLength displayedData.right).symm
                    exact NatDivides_product_closed_unary_hsame_aux zUnary displayedData.left lengthEq
                  have dividesDisplayed : NatDivides p displayed :=
                    Exists.intro s (And.intro sData.left displayedData.right)
                  exact
                    (NatDivides_dividend_hsame_transport dividesDisplayed
                      (hsame_symm sameDisplayed)).right

end BEDC.Derived.PrimeUp
