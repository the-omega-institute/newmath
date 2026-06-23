import BEDC.Derived.PrimeUp
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.ResultCancel
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

def NatEuclidPrime (p : BHist) : Prop :=
  NatPrime p ∧
    ∀ {x y z : BHist}, UnaryHistory x -> UnaryHistory y -> NatMul x y z ->
      NatDivides p z -> NatDivides p x ∨ NatDivides p y

theorem NatEuclidPrime_prime {p : BHist} :
    NatEuclidPrime p -> NatPrime p := by
  intro prime
  exact prime.left

theorem NatEuclidPrime_product_left_or_right {p x y z : BHist} :
    NatEuclidPrime p -> UnaryHistory x -> UnaryHistory y -> NatMul x y z ->
      NatDivides p z -> NatDivides p x ∨ NatDivides p y := by
  intro prime xUnary yUnary product dividesProduct
  exact prime.right xUnary yUnary product dividesProduct

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

theorem NatDivides_multiplier_after_common_multiplicand_cancel
    {a b ab q z : BHist} :
    UnaryHistory a -> (hsame a BHist.Empty -> False) -> UnaryHistory b ->
      NatMul a b ab -> NatMul a q z -> NatDivides ab z -> NatDivides b q := by
  intro aUnary aNonempty bUnary productAB productAQ dividesABZ
  cases dividesABZ with
  | intro r rData =>
      cases rData with
      | intro rUnary productABR =>
          have productBRTotal := NatMul_total bUnary rUnary
          cases productBRTotal with
          | intro br brData =>
              have productABrTotal := NatMul_total aUnary brData.left
              cases productABrTotal with
              | intro displayed displayedData =>
                  have sameDisplayedZ : hsame displayed z :=
                    hsame_symm
                      (NatMul_assoc_hsame aUnary bUnary rUnary productAB productABR
                        brData.right displayedData.right)
                  have sameQBR : hsame q br :=
                    NatMul_nonempty_multiplicand_result_cancel aUnary aNonempty
                      productAQ displayedData.right (hsame_symm sameDisplayedZ)
                  exact
                    (NatDivides_dividend_hsame_transport
                      (Exists.intro r (And.intro rUnary brData.right))
                      (hsame_symm sameQBR)).right

private theorem NatMul_cont_right_distrib_nat_aux (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b :=
      congrArg (fun n => n + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c :=
      congrArg (fun n => a * c + n) (Nat.mul_comm c b)

theorem NatMul_cont_right_distrib {x y z b xb yb zb : BHist} :
    UnaryHistory x -> UnaryHistory y -> UnaryHistory b -> Cont x y z ->
      NatMul x b xb -> NatMul y b yb -> NatMul z b zb -> NatAdd xb yb zb := by
  intro xUnary yUnary bUnary xyCont mulX mulY mulZ
  have zUnary : UnaryHistory z := unary_cont_closed xUnary yUnary xyCont
  have xbUnary : UnaryHistory xb := NatMul_result_unary xUnary mulX
  have ybUnary : UnaryHistory yb := NatMul_result_unary yUnary mulY
  have zbUnary : UnaryHistory zb := NatMul_result_unary zUnary mulZ
  have appendUnary : UnaryHistory (append xb yb) :=
    unary_append_closed xbUnary ybUnary
  have sameZB : hsame zb (append xb yb) := by
    have addXY : NatAdd x y z := And.intro xUnary (And.intro yUnary xyCont)
    have lengthEq :
        BEDC.FKernel.ExternalBinary.bwordLength zb =
          BEDC.FKernel.ExternalBinary.bwordLength (append xb yb) := by
      calc
        BEDC.FKernel.ExternalBinary.bwordLength zb =
            BEDC.FKernel.ExternalBinary.bwordLength z *
              BEDC.FKernel.ExternalBinary.bwordLength b := NatMul_bwordLength mulZ
        _ =
            (BEDC.FKernel.ExternalBinary.bwordLength x +
                BEDC.FKernel.ExternalBinary.bwordLength y) *
              BEDC.FKernel.ExternalBinary.bwordLength b :=
          congrArg (fun n => n * BEDC.FKernel.ExternalBinary.bwordLength b) (NatAdd_length addXY)
        _ =
            BEDC.FKernel.ExternalBinary.bwordLength x *
                BEDC.FKernel.ExternalBinary.bwordLength b +
              BEDC.FKernel.ExternalBinary.bwordLength y *
                BEDC.FKernel.ExternalBinary.bwordLength b :=
          NatMul_cont_right_distrib_nat_aux
            (BEDC.FKernel.ExternalBinary.bwordLength x)
            (BEDC.FKernel.ExternalBinary.bwordLength y)
            (BEDC.FKernel.ExternalBinary.bwordLength b)
        _ =
            BEDC.FKernel.ExternalBinary.bwordLength xb +
              BEDC.FKernel.ExternalBinary.bwordLength y *
                BEDC.FKernel.ExternalBinary.bwordLength b :=
          congrArg
            (fun n =>
              n + BEDC.FKernel.ExternalBinary.bwordLength y *
                BEDC.FKernel.ExternalBinary.bwordLength b)
            (NatMul_bwordLength mulX).symm
        _ =
            BEDC.FKernel.ExternalBinary.bwordLength xb +
              BEDC.FKernel.ExternalBinary.bwordLength yb :=
          congrArg (fun n => BEDC.FKernel.ExternalBinary.bwordLength xb + n)
            (NatMul_bwordLength mulY).symm
        _ = BEDC.FKernel.ExternalBinary.bwordLength (append xb yb) :=
          (BEDC.FKernel.ExternalBinary.bwordLength_append xb yb).symm
    exact (NatUp_unary_standard_bridge.right.right.right.left zbUnary appendUnary).mpr lengthEq
  exact And.intro xbUnary
    (And.intro ybUnary
      (cont_result_hsame_transport (cont_intro rfl) (hsame_symm sameZB)))

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

theorem NatMul_product_factor_quotient {d e q r x y p s z : BHist} :
    UnaryHistory d -> UnaryHistory e -> UnaryHistory q -> UnaryHistory r ->
      NatMul d q x -> NatMul e r y -> NatMul d e p -> NatMul q r s ->
        NatMul x y z -> NatMul p s z := by
  intro dUnary eUnary qUnary rUnary productDQ productER productDE productQR productXY
  have pUnary : UnaryHistory p := NatMul_result_unary dUnary productDE
  have sUnary : UnaryHistory s := NatMul_result_unary qUnary productQR
  have displayedTotal := NatMul_total pUnary sUnary
  cases displayedTotal with
  | intro displayed displayedData =>
      have xUnary : UnaryHistory x := NatMul_result_unary dUnary productDQ
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
                (fun n => n * BEDC.FKernel.ExternalBinary.bwordLength y)
                (NatMul_bwordLength productDQ) |>.trans
                (congrArg
                  (fun n =>
                    (BEDC.FKernel.ExternalBinary.bwordLength d *
                      BEDC.FKernel.ExternalBinary.bwordLength q) * n)
                  (NatMul_bwordLength productER))
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
                  (NatMul_bwordLength productQR).symm)
            _ = BEDC.FKernel.ExternalBinary.bwordLength displayed :=
              (NatMul_bwordLength displayedData.right).symm
        exact NatDivides_product_closed_unary_hsame_aux zUnary displayedData.left lengthEq
      exact (NatMul_result_hsame_transport displayedData.right (hsame_symm sameDisplayed)).right

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
