import BEDC.Derived.PrimeUp
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.DivisionWithRemainder
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

theorem NatUnary_nonempty_positive_for_divides_closure {d : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) ->
      NatUnaryStrictPrefix BHist.Empty d := by
  intro dUnary dNonempty
  cases d with
  | Empty =>
      exact False.elim (dNonempty rfl)
  | e0 dTail =>
      cases dUnary
  | e1 dTail =>
      exact ⟨BHist.e1 dTail, dUnary, (fun empty => by cases empty), cont_left_unit _⟩

theorem NatUnaryStrictPrefix_hsame_source_transport_for_divides_closure {d d' b : BHist} :
    NatUnaryStrictPrefix d b -> hsame d d' -> NatUnaryStrictPrefix d' b := by
  intro strict sameSource
  cases strict with
  | intro tail data =>
      exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left data.right.right
        sameSource (hsame_refl b)

theorem NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure {d b b' : BHist} :
    NatUnaryStrictPrefix d b -> hsame b b' -> NatUnaryStrictPrefix d b' := by
  intro strict sameTarget
  cases strict with
  | intro tail data =>
      exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left data.right.right
        (hsame_refl d) sameTarget

theorem NatUnaryStrictPrefix_trans {a b c : BHist} :
    NatUnaryStrictPrefix a b -> NatUnaryStrictPrefix b c -> NatUnaryStrictPrefix a c := by
  intro left right
  cases NatUnaryStrictPrefix_trans_composite_tail left right with
  | intro _tail data =>
      exact data.right.right.right

theorem NatUnaryStrictPrefix_successor_boundary_local {d n : BHist} :
    UnaryHistory d -> NatUnaryStrictPrefix d (BHist.e1 n) ->
      hsame d n ∨ NatUnaryStrictPrefix d n := by
  intro dUnary strict
  cases strict with
  | intro tail data =>
      cases data with
      | intro tailUnary strictData =>
          cases strictData with
          | intro tailNonempty tailCont =>
              cases tail with
              | Empty =>
                  exact False.elim (tailNonempty rfl)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  cases tail with
                  | Empty =>
                      have sameDN : hsame d n := by
                        cases d with
                        | Empty =>
                            cases tailCont
                            rfl
                        | e0 dTail =>
                            cases dUnary
                        | e1 dTail =>
                            exact (append_empty_right (BHist.e1 dTail)).symm.trans
                              (BHist.e1.inj tailCont).symm
                      exact Or.inl sameDN
                  | e0 tailTail =>
                      exact False.elim (unary_no_zero_extension (unary_e1_inversion tailUnary))
                  | e1 tailTail =>
                      have shorterCont : Cont d (BHist.e1 tailTail) n := by
                        exact cont_intro (BHist.e1.inj tailCont)
                      exact Or.inr
                        ⟨BHist.e1 tailTail, unary_e1_inversion tailUnary,
                          (fun empty => by cases empty), shorterCont⟩

theorem NatUnary_nonempty_length_pos {d : BHist} :
    UnaryHistory d -> (d = BHist.Empty -> False) ->
      0 < BEDC.FKernel.ExternalBinary.bwordLength d := by
  intro dUnary dNonempty
  cases d with
  | Empty =>
      exact False.elim (dNonempty rfl)
  | e0 dTail =>
      cases dUnary
  | e1 dTail =>
      exact Nat.succ_pos _

theorem NatUnaryStrictPrefix_length_lt {h k : BHist} :
    UnaryHistory h -> NatUnaryStrictPrefix h k ->
      BEDC.FKernel.ExternalBinary.bwordLength h <
        BEDC.FKernel.ExternalBinary.bwordLength k := by
  intro hUnary strict
  cases strict with
  | intro tail data =>
      have tailPositive :=
        NatUnary_nonempty_length_pos data.left data.right.left
      have lengthK :
          BEDC.FKernel.ExternalBinary.bwordLength k =
            BEDC.FKernel.ExternalBinary.bwordLength h +
              BEDC.FKernel.ExternalBinary.bwordLength tail :=
        NatUp_unary_standard_bridge.right.right.right.right hUnary data.left data.right.right
      rw [lengthK]
      exact Nat.lt_add_of_pos_right tailPositive

theorem NatStrongInduction {P : BHist -> Prop}
    (step :
      ∀ n : BHist, UnaryHistory n ->
        (∀ r : BHist, UnaryHistory r -> NatUnaryStrictPrefix r n -> P r) -> P n) :
    ∀ n : BHist, UnaryHistory n -> P n := by
  intro n nUnary
  have byLength :
      ∀ m : Nat, ∀ h : BHist, UnaryHistory h ->
        BEDC.FKernel.ExternalBinary.bwordLength h = m -> P h := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro h hUnary hLength
        exact step h hUnary
          (fun r rUnary rStrict =>
            have rLtH := NatUnaryStrictPrefix_length_lt rUnary rStrict
            have rLtM : BEDC.FKernel.ExternalBinary.bwordLength r < m := by
              rw [hLength] at rLtH
              exact rLtH
            ih (BEDC.FKernel.ExternalBinary.bwordLength r) rLtM r rUnary rfl)
  exact byLength (BEDC.FKernel.ExternalBinary.bwordLength n) n nUnary rfl

theorem NatAdd_left_positive_right_strict {x y s : BHist} :
    NatAdd x y s -> NatUnaryStrictPrefix BHist.Empty x -> NatUnaryStrictPrefix y s := by
  intro add xPositive
  have xNonempty : x = BHist.Empty -> False := by
    intro xEmpty
    cases xEmpty
    exact NatUnaryStrictPrefix_empty_right_absurd xPositive
  exact ⟨x, add.left, xNonempty, cont_intro
    (add.right.right.trans (unary_append_comm add.left add.right.left))⟩

theorem NatAdd_right_positive_left_strict {x y s : BHist} :
    NatAdd x y s -> NatUnaryStrictPrefix BHist.Empty y -> NatUnaryStrictPrefix x s := by
  intro add yPositive
  have yNonempty : y = BHist.Empty -> False := by
    intro yEmpty
    cases yEmpty
    exact NatUnaryStrictPrefix_empty_right_absurd yPositive
  exact ⟨y, add.right.left, yNonempty, add.right.right⟩

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

theorem NatDivides_mul_right_factor_closed {d q x z : BHist} :
    UnaryHistory x -> NatDivides d q -> NatMul q x z -> NatDivides d z := by
  intro xUnary divides product
  have qUnary : UnaryHistory q := NatDivides_result_unary divides
  have reverseTotal := NatMul_total xUnary qUnary
  cases reverseTotal with
  | intro z' zData =>
      have sameZ : hsame z z' := NatMul_comm_hsame qUnary xUnary product zData.right
      have dividesZ' : NatDivides d z' := NatDivides_mul_left_closed xUnary divides zData.right
      exact (NatDivides_dividend_hsame_transport dividesZ' (hsame_symm sameZ)).right

theorem NatMul_factor_left_product_divides {p q b pq pqb : BHist} :
    UnaryHistory p -> NatMul p q pq -> NatMul pq b pqb -> NatDivides p pqb := by
  intro _pUnary mulPQ mulPQB
  have pDividesPQ : NatDivides p pq := ⟨q, NatMul_right_unary mulPQ, mulPQ⟩
  exact NatDivides_mul_right_factor_closed (NatMul_right_unary mulPQB) pDividesPQ mulPQB

theorem NatDivides_product_left_factor_extension {p a b q ab aq aqb : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory q ->
      NatMul a b ab -> NatMul a q aq -> NatMul aq b aqb ->
        NatDivides p ab -> NatDivides p aqb := by
  intro aUnary bUnary qUnary mulAB mulAQ mulAQB dividesAB
  have abUnary : UnaryHistory ab := NatMul_result_unary aUnary mulAB
  have aqUnary : UnaryHistory aq := NatMul_result_unary aUnary mulAQ
  have abqTotal := NatMul_total abUnary qUnary
  cases abqTotal with
  | intro abq abqData =>
      have qbTotal := NatMul_total qUnary bUnary
      cases qbTotal with
      | intro qb qbData =>
          have bqTotal := NatMul_total bUnary qUnary
          cases bqTotal with
          | intro bq bqData =>
              have aqbAssocTotal := NatMul_total aUnary qbData.left
              cases aqbAssocTotal with
              | intro aqbAssoc aqbAssocData =>
                  have abqAssocTotal := NatMul_total aUnary bqData.left
                  cases abqAssocTotal with
                  | intro abqAssoc abqAssocData =>
                      have sameAQB_AQB :
                          hsame aqb aqbAssoc :=
                        NatMul_assoc_hsame aUnary qUnary bUnary
                          mulAQ mulAQB qbData.right aqbAssocData.right
                      have sameQB_BQ :
                          hsame qb bq :=
                        NatMul_comm_hsame qUnary bUnary qbData.right bqData.right
                      have aqbAssocAsBq :
                          NatMul a bq aqbAssoc :=
                        (NatMul_multiplier_hsame_transport aqbAssocData.right sameQB_BQ).right
                      have sameAQBAssoc_ABQAssoc :
                          hsame aqbAssoc abqAssoc :=
                        NatMul_functional aUnary aqbAssocAsBq abqAssocData.right
                      have sameABQ_ABQAssoc :
                          hsame abq abqAssoc :=
                        NatMul_assoc_hsame aUnary bUnary qUnary
                          mulAB abqData.right bqData.right abqAssocData.right
                      have dividesABQ : NatDivides p abq :=
                        NatDivides_mul_right_factor_closed qUnary dividesAB abqData.right
                      exact
                        (NatDivides_dividend_hsame_transport dividesABQ
                          (hsame_trans sameABQ_ABQAssoc
                            (hsame_trans (hsame_symm sameAQBAssoc_ABQAssoc)
                              (hsame_symm sameAQB_AQB)))).right

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

theorem NatMul_add_right_distrib {x y s b xb yb sb : BHist} :
    NatAdd x y s -> NatMul s b sb -> NatMul x b xb -> NatMul y b yb ->
      NatAdd xb yb sb := by
  intro add mulS mulX mulY
  exact NatMul_cont_right_distrib add.left add.right.left (NatMul_right_unary mulS)
    add.right.right mulX mulY mulS

theorem NatDivRem_tail_product_divides {p a b q r z rb : BHist} :
    NatPrime p -> UnaryHistory b -> NatDivRem p a q r -> NatMul a b z ->
      NatMul r b rb -> NatDivides p z -> NatDivides p rb := by
  intro prime bUnary divrem product rbMul dividesProduct
  cases divrem with
  | intro pq data =>
      have pUnary : UnaryHistory p := prime.left
      have pNonempty : hsame p BHist.Empty -> False := NatPrime_empty_absurd prime
      have pqUnary : UnaryHistory pq := NatMul_result_unary pUnary data.left
      have pqbTotal := NatMul_total pqUnary bUnary
      cases pqbTotal with
      | intro pqb pqbData =>
          have addProducts : NatAdd pqb rb z := by
            exact NatMul_add_right_distrib data.right.left product pqbData.right rbMul
          have pDividesPQB : NatDivides p pqb :=
            NatMul_factor_left_product_divides pUnary data.left pqbData.right
          exact dvd_tail_of_dvd_sum pUnary pNonempty addProducts pDividesPQB dividesProduct

theorem NatPrime_no_counterexample {p a b z : BHist} :
    NatPrime p -> UnaryHistory a -> UnaryHistory b -> NatMul a b z -> NatDivides p z ->
      (NatDivides p a -> False) -> (NatDivides p b -> False) -> False := by
  intro prime aUnary bUnary product dividesProduct notDvdA notDvdB
  refine NatStrongInduction
    (P := fun a => ∀ b z : BHist, UnaryHistory b -> NatMul a b z -> NatDivides p z ->
      (NatDivides p a -> False) -> (NatDivides p b -> False) -> False) ?_ a aUnary
    b z bUnary product dividesProduct notDvdA notDvdB
  intro a aUnary ih b z bUnary product dividesProduct notDvdA notDvdB
  have pNonempty : hsame p BHist.Empty -> False := NatPrime_empty_absurd prime
  have divremExists := divRem_exists (M := p) (n := a) prime.left aUnary pNonempty
  cases divremExists with
  | intro q remData =>
      cases remData with
      | intro r divrem =>
          have remUnary : UnaryHistory r := NatDivRem_remainder_unary divrem
          have remLtP : NatUnaryStrictPrefix r p := by
            cases divrem with
            | intro _pq data =>
                exact data.right.right
          have dvdAiff := dvd_iff_rem_zero prime.left pNonempty divrem
          cases r with
          | Empty =>
              exact notDvdA (dvdAiff.mpr rfl)
          | e0 rTail =>
              cases remUnary
          | e1 rTail =>
              have rPositive : NatUnaryStrictPrefix BHist.Empty (BHist.e1 rTail) :=
                NatUnary_nonempty_positive_for_divides_closure remUnary (fun h => not_hsame_e1_empty h)
              have rbTotal := NatMul_total remUnary bUnary
              cases rbTotal with
              | intro rb rbData =>
                  have pDividesRB : NatDivides p rb :=
                    NatDivRem_tail_product_divides prime bUnary divrem product rbData.right
                      dividesProduct
                  have notDvdR : NatDivides p (BHist.e1 rTail) -> False :=
                    not_dvd_of_pos_lt prime.left remUnary prime.right.left rPositive remLtP
                  cases q with
                  | Empty =>
                      have sameA : hsame a (BHist.e1 rTail) := by
                        cases divrem with
                        | intro pq data =>
                            cases data.left with
                            | zero _pUnary =>
                                exact cont_left_unit_result data.right.left.right.right
                      have aPositive : NatUnaryStrictPrefix BHist.Empty a :=
                        NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure rPositive (hsame_symm sameA)
                      have aLtP : NatUnaryStrictPrefix a p :=
                        NatUnaryStrictPrefix_hsame_source_transport_for_divides_closure remLtP (hsame_symm sameA)
                      have aNonempty : hsame a BHist.Empty -> False := by
                        intro aEmpty
                        cases aEmpty
                        exact NatUnaryStrictPrefix_empty_right_absurd aPositive
                      have aNonunit : hsame a (BHist.e1 BHist.Empty) -> False := by
                        intro aUnit
                        have unitMul : NatMul (BHist.e1 BHist.Empty) b z :=
                          (NatMul_multiplicand_hsame_transport aUnit product).right
                        have sameZB : hsame z b := NatMul_unit_left_hsame bUnary unitMul
                        exact notDvdB
                          ((NatDivides_dividend_hsame_transport dividesProduct sameZB).right)
                      have unitLtA : NatUnaryStrictPrefix (BHist.e1 BHist.Empty) a := by
                        have unitUnary : UnaryHistory (BHist.e1 BHist.Empty) :=
                          unary_e1_closed unary_empty
                        have total := NatUnaryPrefix_trichotomy_hsame_strict unitUnary aUnary
                        cases total with
                        | inl sameUnitA =>
                            exact False.elim (aNonunit (hsame_symm sameUnitA))
                        | inr rest =>
                            cases rest with
                            | inl unitLt =>
                                exact unitLt
                            | inr aLtUnit =>
                                have emptyOrStrict :=
                                  NatUnaryStrictPrefix_successor_boundary_local aUnary aLtUnit
                                cases emptyOrStrict with
                                | inl aEmpty =>
                                    exact False.elim (aNonempty aEmpty)
                                | inr aLtEmpty =>
                                    exact False.elim
                                      (NatUnaryStrictPrefix_empty_right_absurd aLtEmpty)
                      have divremPByA :=
                        divRem_exists (M := a) (n := p) aUnary prime.left aNonempty
                      cases divremPByA with
                      | intro q2 q2Data =>
                          cases q2Data with
                          | intro r2 divrem2 =>
                              have r2Unary : UnaryHistory r2 := NatDivRem_remainder_unary divrem2
                              have r2LtA : NatUnaryStrictPrefix r2 a := by
                                cases divrem2 with
                                | intro _aq data =>
                                    exact data.right.right
                              have dvdPByAiff := dvd_iff_rem_zero aUnary aNonempty divrem2
                              cases r2 with
                              | Empty =>
                                  have aDividesP : NatDivides a p := dvdPByAiff.mpr rfl
                                  exact prime_no_proper_divisor prime aUnary unitLtA aLtP aDividesP
                              | e0 r2Tail =>
                                  cases r2Unary
                              | e1 r2Tail =>
                                  have r2Positive :
                                      NatUnaryStrictPrefix BHist.Empty (BHist.e1 r2Tail) :=
                                    NatUnary_nonempty_positive_for_divides_closure r2Unary
                                      (fun h => not_hsame_e1_empty h)
                                  have r2bTotal := NatMul_total r2Unary bUnary
                                  cases r2bTotal with
                                  | intro r2b r2bData =>
                                      have pbTotal := NatMul_total prime.left bUnary
                                      cases pbTotal with
                                      | intro pb pbData =>
                                          have pDividesPB : NatDivides p pb :=
                                            ⟨b, bUnary, pbData.right⟩
                                          cases divrem2 with
                                          | intro aq data2 =>
                                              have aqbTotal :=
                                                NatMul_total
                                                  (NatMul_result_unary aUnary data2.left) bUnary
                                              cases aqbTotal with
                                              | intro aqb aqbData =>
                                                  have addProducts : NatAdd aqb r2b pb :=
                                                    NatMul_add_right_distrib data2.right.left
                                                      pbData.right aqbData.right r2bData.right
                                                  have pDividesAQB : NatDivides p aqb :=
                                                    NatDivides_product_left_factor_extension
                                                      aUnary bUnary (NatMul_right_unary data2.left)
                                                      product data2.left aqbData.right dividesProduct
                                                  have pDividesR2B : NatDivides p r2b :=
                                                    dvd_tail_of_dvd_sum prime.left
                                                      (NatPrime_empty_absurd prime)
                                                      addProducts pDividesAQB pDividesPB
                                                  have notDvdR2 :
                                                      NatDivides p (BHist.e1 r2Tail) -> False :=
                                                    fun dividesR2 =>
                                                      not_dvd_of_pos_lt prime.left r2Unary
                                                        prime.right.left r2Positive
                                                        (NatUnaryStrictPrefix_trans r2LtA aLtP)
                                                        dividesR2
                                                  exact ih (BHist.e1 r2Tail) r2Unary r2LtA b r2b
                                                    bUnary r2bData.right pDividesR2B notDvdR2 notDvdB
                  | e0 qTail =>
                      have qUnary := NatDivRem_quotient_unary divrem
                      cases qUnary
                  | e1 qTail =>
                      have rLtA : NatUnaryStrictPrefix (BHist.e1 rTail) a := by
                        cases divrem with
                        | intro pq data =>
                            have pqPositive : NatUnaryStrictPrefix BHist.Empty pq := by
                              have pqNonempty : hsame pq BHist.Empty -> False := by
                                intro pqEmpty
                                cases pqEmpty
                                cases data.left with
                                | succ prev step =>
                                    exact pNonempty
                                      (NatMul_succ_result_empty_left_empty
                                        (NatMul.succ prev step) rfl)
                              exact NatUnary_nonempty_positive_for_divides_closure
                                (NatMul_result_unary prime.left data.left) pqNonempty
                            exact NatAdd_left_positive_right_strict data.right.left pqPositive
                      exact ih (BHist.e1 rTail) remUnary rLtA b rb bUnary rbData.right
                        pDividesRB notDvdR notDvdB

theorem NatPrime_divides_or_not {p n : BHist} :
    NatPrime p -> UnaryHistory n -> NatDivides p n ∨ (NatDivides p n -> False) := by
  intro prime nUnary
  have pNonempty : hsame p BHist.Empty -> False := NatPrime_empty_absurd prime
  have divremExists := divRem_exists (M := p) (n := n) prime.left nUnary pNonempty
  cases divremExists with
  | intro q qData =>
      cases qData with
      | intro r divrem =>
          have dvdIff := dvd_iff_rem_zero prime.left pNonempty divrem
          cases r with
          | Empty =>
              exact Or.inl (dvdIff.mpr rfl)
          | e0 rTail =>
              cases NatDivRem_remainder_unary divrem
          | e1 rTail =>
              have rPositive : NatUnaryStrictPrefix BHist.Empty (BHist.e1 rTail) :=
                NatUnary_nonempty_positive_for_divides_closure (NatDivRem_remainder_unary divrem)
                  (fun h => not_hsame_e1_empty h)
              exact Or.inr (not_dvd_of_rem_pos prime.left pNonempty divrem rPositive)

theorem NatPrime.toNatEuclidPrime {p : BHist} :
    NatPrime p -> NatEuclidPrime p := by
  intro prime
  constructor
  · exact prime
  · intro x y z xUnary yUnary product dividesProduct
    have xCases := NatPrime_divides_or_not prime xUnary
    cases xCases with
    | inl dividesX =>
        exact Or.inl dividesX
    | inr notDividesX =>
        have yCases := NatPrime_divides_or_not prime yUnary
        cases yCases with
        | inl dividesY =>
            exact Or.inr dividesY
        | inr notDividesY =>
            exact False.elim
              (NatPrime_no_counterexample prime xUnary yUnary product dividesProduct
                notDividesX notDividesY)

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
