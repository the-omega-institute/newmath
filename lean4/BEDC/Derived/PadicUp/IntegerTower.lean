import BEDC.Derived.PadicUp.Multiplicative
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def zpuNatToUnary : Nat -> BHist :=
  BEDC.Derived.IntUp.natToUnary

theorem zpuNatToUnary_unary (n : Nat) : UnaryHistory (zpuNatToUnary n) :=
  BEDC.Derived.IntUp.natToUnary_unary n

theorem zpuNatToUnary_length (n : Nat) : bwordLength (zpuNatToUnary n) = n :=
  BEDC.Derived.IntUp.natToUnary_length n

theorem zpu_hsame_of_unary_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

theorem zpu_natToUnary_hsame_of_length {h : BHist} :
    UnaryHistory h -> hsame (zpuNatToUnary (bwordLength h)) h := by
  intro hUnary
  exact zpu_hsame_of_unary_length (zpuNatToUnary_unary _) hUnary
    (zpuNatToUnary_length _)

theorem NatUnaryStrictPrefix_of_length_lt {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h < bwordLength k ->
      NatUnaryStrictPrefix h k := by
  intro hUnary kUnary lengthLt
  have total := NatUnaryPrefix_total hUnary kUnary
  cases total with
  | inl left =>
      cases left with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp same
              exact False.elim (Nat.lt_irrefl _ (lengthEq ▸ lengthLt))
          | inr strict =>
              exact strict
  | inr right =>
      cases right with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp
                  (hsame_symm same)
              exact False.elim (Nat.lt_irrefl _ (lengthEq ▸ lengthLt))
          | inr strictKH =>
              have kLtH := NatUnaryStrictPrefix_length_lt kUnary strictKH
              exact False.elim (Nat.lt_asymm lengthLt kLtH)

theorem NatUnaryStrictPrefix_succ_of_not_boundary {M r : BHist} :
    UnaryHistory M -> UnaryHistory r -> NatUnaryStrictPrefix r M ->
      (hsame (BHist.e1 r) M -> False) -> NatUnaryStrictPrefix (BHist.e1 r) M := by
  intro MUnary rUnary rLtM notBoundary
  have nextUnary : UnaryHistory (BHist.e1 r) := unary_e1_closed rUnary
  have total := NatUnaryPrefix_total nextUnary MUnary
  cases total with
  | inl nextPrefix =>
      cases nextPrefix with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl sameNextM =>
              exact False.elim (notBoundary sameNextM)
          | inr nextLtM =>
              exact nextLtM
  | inr reversePrefix =>
      cases reversePrefix with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl sameMNext =>
              exact False.elim (notBoundary (hsame_symm sameMNext))
          | inr MLtNext =>
              have nextNotLtM : NatUnaryStrictPrefix (BHist.e1 r) M -> False := by
                intro nextLtM
                exact NatUnaryStrictPrefix_asymm nextLtM MLtNext
              exact False.elim
                (notBoundary (zero_or_succ_boundary MUnary rUnary rLtM nextNotLtM))

theorem zpuNatToUnary_NatMul_rel (a b : Nat) :
    NatMul (zpuNatToUnary a) (zpuNatToUnary b) (zpuNatToUnary (a * b)) := by
  have leftUnary := zpuNatToUnary_unary a
  have rightUnary := zpuNatToUnary_unary b
  have total := NatMul_total leftUnary rightUnary
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (zpuNatToUnary (a * b)) :=
        zpu_hsame_of_unary_length resultData.left (zpuNatToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans
            (by rw [zpuNatToUnary_length, zpuNatToUnary_length, zpuNatToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

def pPowCanon (p N : BHist) : BHist :=
  zpuNatToUnary (bwordLength p ^ bwordLength N)

theorem pPowCanon_unary (p N : BHist) : UnaryHistory (pPowCanon p N) :=
  zpuNatToUnary_unary _

theorem pPowCanon_length (p N : BHist) :
    bwordLength (pPowCanon p N) = bwordLength p ^ bwordLength N :=
  zpuNatToUnary_length _

theorem pPowCanon_PPow {p N : BHist} :
    UnaryHistory p -> UnaryHistory N -> PPow p N (pPowCanon p N) := by
  intro pUnary NUnary
  induction N with
  | Empty =>
      change PPow p BHist.Empty (zpuNatToUnary (bwordLength p ^ 0))
      have sameOne : hsame (zpuNatToUnary (bwordLength p ^ 0)) NatOne :=
        zpu_hsame_of_unary_length (zpuNatToUnary_unary _) (unary_e1_closed unary_empty)
          (by rw [zpuNatToUnary_length]; rfl)
      exact PPow_result_hsame_transport (PPow.zero pUnary) (hsame_symm sameOne)
  | e0 _ _ =>
      cases NUnary
  | e1 tail ih =>
      have tailUnary : UnaryHistory tail := unary_e1_inversion NUnary
      have prevPow := ih tailUnary
      have raw :
          NatMul (zpuNatToUnary (bwordLength p))
            (zpuNatToUnary (bwordLength p ^ bwordLength tail))
            (zpuNatToUnary (bwordLength p * bwordLength p ^ bwordLength tail)) :=
        zpuNatToUnary_NatMul_rel _ _
      have sameP : hsame (zpuNatToUnary (bwordLength p)) p :=
        zpu_natToUnary_hsame_of_length pUnary
      have sameResult :
          hsame (zpuNatToUnary (bwordLength p * bwordLength p ^ bwordLength tail))
            (pPowCanon p (BHist.e1 tail)) :=
        zpu_hsame_of_unary_length (zpuNatToUnary_unary _) (pPowCanon_unary p (BHist.e1 tail))
          (by
            rw [zpuNatToUnary_length, pPowCanon_length]
            rw [NatUp_unary_standard_bridge.right.left tail tailUnary]
            rw [Nat.pow_succ]
            exact Nat.mul_comm _ _)
      have step :
          NatMul p (pPowCanon p tail) (pPowCanon p (BHist.e1 tail)) :=
        (NatMul_operation_congruence raw sameP (hsame_refl _) sameResult).left
      exact PPow.succ prevPow step

theorem pPowCanon_nonempty_of_prime {p N : BHist} :
    NatPrime p -> UnaryHistory N -> hsame (pPowCanon p N) BHist.Empty -> False := by
  intro prime NUnary emptyPower
  exact PPow_nonempty_result (NatPrime_empty_absurd prime)
    (pPowCanon_PPow prime.left NUnary) emptyPower

theorem pPowCanon_positive_of_prime {p N : BHist} :
    NatPrime p -> UnaryHistory N -> 0 < bwordLength (pPowCanon p N) := by
  intro prime NUnary
  cases Nat.eq_zero_or_pos (bwordLength (pPowCanon p N)) with
  | inl zeroLen =>
      have emptyPower : hsame (pPowCanon p N) BHist.Empty :=
        zpu_hsame_of_unary_length (pPowCanon_unary p N) unary_empty
          (zeroLen.trans (NatUp_unary_standard_bridge.left).symm)
      exact False.elim (pPowCanon_nonempty_of_prime prime NUnary emptyPower)
  | inr positive =>
      exact positive

def NatUnaryPrefix (h k : BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧ Cont h tail k

theorem pow_dvd_pow_of_le {p N K : BHist}
    (prime : NatPrime p) (NUnary : UnaryHistory N) (_KUnary : UnaryHistory K)
    (pref : NatUnaryPrefix N K) :
      NatDivides (pPowCanon p N) (pPowCanon p K) := by
  cases pref with
  | intro tail tailData =>
      have tailUnary : UnaryHistory tail := tailData.left
      have KAdd : NatAdd N tail K := ⟨NUnary, tailUnary, tailData.right⟩
      have powN := pPowCanon_PPow prime.left NUnary
      have powTail := pPowCanon_PPow prime.left tailUnary
      have pNUnary := pPowCanon_unary p N
      have pTailUnary := pPowCanon_unary p tail
      have productTotal := NatMul_total pNUnary pTailUnary
      cases productTotal with
      | intro product productData =>
          have powKProduct : PPow p K product :=
            PPow_add powN powTail KAdd productData.right
          have powKCanon := pPowCanon_PPow prime.left
            (NatAdd_result_unary KAdd)
          have sameProduct : hsame product (pPowCanon p K) :=
            PPow_functional powKProduct powKCanon
          exact ⟨pPowCanon p tail, pTailUnary,
            (NatMul_result_hsame_transport productData.right sameProduct).right⟩

theorem rem_rem_of_dvd {M K n qK rK qM rM qNested rNested : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      NatDivides M K ->
      NatDivRem K n qK rK ->
        NatDivRem M n qM rM ->
          NatDivRem M rK qNested rNested ->
            hsame rNested rM := by
  intro MUnary MNonempty dividesMK divremK divremM divremNested
  cases divremK with
  | intro kq kData =>
      have dividesKQ : NatDivides M kq := by
        exact NatDivides_mul_right_factor_closed (NatDivRem_quotient_unary ⟨kq, kData⟩)
          dividesMK kData.left
      cases divremNested with
      | intro nestedProduct nestedData =>
          have dividesNestedProductByM : NatDivides M nestedProduct :=
            ⟨qNested, NatMul_right_unary nestedData.left, nestedData.left⟩
          have displayedNested :
              Cont (BEDC.FKernel.Cont.append kq nestedProduct) rNested n := by
            exact cont_intro
              (by
                calc
                  n = BEDC.FKernel.Cont.append kq rK := kData.right.left.right.right
                  _ = BEDC.FKernel.Cont.append kq
                        (BEDC.FKernel.Cont.append nestedProduct rNested) :=
                    congrArg (fun h => BEDC.FKernel.Cont.append kq h)
                      nestedData.right.left.right.right
                  _ = BEDC.FKernel.Cont.append
                        (BEDC.FKernel.Cont.append kq nestedProduct) rNested :=
                    (BEDC.FKernel.Cont.append_assoc kq nestedProduct rNested).symm)
          have dividesDisplayedProduct : NatDivides M (BEDC.FKernel.Cont.append kq nestedProduct) :=
            NatDivides_cont_closed dividesKQ dividesNestedProductByM (cont_intro rfl)
          cases dividesDisplayedProduct with
          | intro displayedQuotient displayedQuotientData =>
              have displayedDirect :
                  NatAdd (BEDC.FKernel.Cont.append kq nestedProduct) rNested n :=
                ⟨NatMul_result_unary MUnary displayedQuotientData.right,
                  NatAdd_right_unary nestedData.right.left,
                  displayedNested⟩
              have synthetic : NatDivRem M n displayedQuotient rNested :=
                ⟨BEDC.FKernel.Cont.append kq nestedProduct, displayedQuotientData.right,
                  displayedDirect, nestedData.right.right⟩
              exact (divRem_unique MUnary MNonempty synthetic divremM).right

def natDivRemFn (M : BHist) : BHist -> BHist × BHist
  | BHist.Empty => (BHist.Empty, BHist.Empty)
  | BHist.e0 _ => (BHist.Empty, BHist.Empty)
  | BHist.e1 n =>
      let previous := natDivRemFn M n
      let nextR := BHist.e1 previous.2
      if _boundary : nextR = M then
        (BHist.e1 previous.1, BHist.Empty)
      else
        (previous.1, nextR)

def natQuotFn (M n : BHist) : BHist :=
  (natDivRemFn M n).1

def natModFn (M n : BHist) : BHist :=
  (natDivRemFn M n).2

theorem natDivRemFn_empty (M : BHist) :
    natDivRemFn M BHist.Empty = (BHist.Empty, BHist.Empty) :=
  rfl

theorem natDivRemFn_e1_boundary {M n q r : BHist}
    (previous : natDivRemFn M n = (q, r)) (boundary : BHist.e1 r = M) :
      natDivRemFn M (BHist.e1 n) = (BHist.e1 q, BHist.Empty) := by
  unfold natDivRemFn
  rw [previous]
  dsimp
  rw [if_pos boundary]

theorem natDivRemFn_e1_inside {M n q r : BHist}
    (previous : natDivRemFn M n = (q, r)) (inside : BHist.e1 r = M -> False) :
      natDivRemFn M (BHist.e1 n) = (q, BHist.e1 r) := by
  unfold natDivRemFn
  rw [previous]
  dsimp
  rw [if_neg inside]

theorem Cont_right_e1 {h k r : BHist} :
    Cont h k r -> Cont h (BHist.e1 k) (BHist.e1 r) := by
  intro cont
  cases cont
  rfl

theorem natDivRemFn_spec_pair {M n : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      NatDivRem M n (natQuotFn M n) (natModFn M n) := by
  intro MUnary nUnary MNonempty
  induction n with
  | Empty =>
      change NatDivRem M BHist.Empty BHist.Empty BHist.Empty
      exact ⟨BHist.Empty, NatMul.zero MUnary,
        And.intro unary_empty (And.intro unary_empty (cont_right_unit BHist.Empty)),
        ⟨M, MUnary, MNonempty, cont_left_unit M⟩⟩
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      have tailUnary : UnaryHistory tail := unary_e1_inversion nUnary
      have prevDivrem :
          NatDivRem M tail (natQuotFn M tail) (natModFn M tail) :=
        ih tailUnary
      have rUnary : UnaryHistory (natModFn M tail) :=
        NatDivRem_remainder_unary prevDivrem
      have rStrict : NatUnaryStrictPrefix (natModFn M tail) M := by
        cases prevDivrem with
        | intro _mq data =>
            exact data.right.right
      by_cases boundary : BHist.e1 (natModFn M tail) = M
      · have stepEq :
            natDivRemFn M (BHist.e1 tail) =
              (BHist.e1 (natQuotFn M tail), BHist.Empty) :=
          natDivRemFn_e1_boundary (M := M) (n := tail)
            (q := natQuotFn M tail) (r := natModFn M tail) rfl boundary
        change NatDivRem M (BHist.e1 tail)
          (natDivRemFn M (BHist.e1 tail)).1
          (natDivRemFn M (BHist.e1 tail)).2
        rw [stepEq]
        cases prevDivrem with
        | intro mq data =>
            have stepCont : Cont mq M (BHist.e1 tail) := by
              exact cont_hsame_transport (hsame_refl mq) boundary
                (hsame_refl (BHist.e1 tail))
                (Cont_right_e1 data.right.left.right.right)
            exact ⟨BHist.e1 tail, NatMul.succ data.left stepCont,
              And.intro nUnary (And.intro unary_empty (cont_right_unit (BHist.e1 tail))),
              ⟨M, MUnary, MNonempty, cont_left_unit M⟩⟩
      · have stepEq :
            natDivRemFn M (BHist.e1 tail) =
              (natQuotFn M tail, BHist.e1 (natModFn M tail)) :=
          natDivRemFn_e1_inside (M := M) (n := tail)
            (q := natQuotFn M tail) (r := natModFn M tail) rfl boundary
        change NatDivRem M (BHist.e1 tail)
          (natDivRemFn M (BHist.e1 tail)).1
          (natDivRemFn M (BHist.e1 tail)).2
        rw [stepEq]
        cases prevDivrem with
        | intro mq data =>
            have nextCont : Cont mq (BHist.e1 (natModFn M tail)) (BHist.e1 tail) := by
              exact Cont_right_e1 data.right.left.right.right
            exact ⟨mq, data.left,
              And.intro (NatMul_result_unary MUnary data.left)
                (And.intro (unary_e1_closed rUnary) nextCont),
              NatUnaryStrictPrefix_succ_of_not_boundary MUnary rUnary rStrict boundary⟩

theorem natModFn_spec {M n : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      NatDivRem M n (natQuotFn M n) (natModFn M n) :=
  natDivRemFn_spec_pair

theorem natModFn_unary {M n : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      UnaryHistory (natModFn M n) := by
  intro MUnary nUnary MNonempty
  exact NatDivRem_remainder_unary (natModFn_spec MUnary nUnary MNonempty)

theorem natModFn_lt {M n : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      NatUnaryStrictPrefix (natModFn M n) M := by
  intro MUnary nUnary MNonempty
  cases natModFn_spec MUnary nUnary MNonempty with
  | intro _mq data =>
      exact data.right.right

theorem natModFn_unique {M n q r : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      NatDivRem M n q r -> hsame (natQuotFn M n) q ∧ hsame (natModFn M n) r := by
  intro MUnary nUnary MNonempty divrem
  exact divRem_unique MUnary MNonempty (natModFn_spec MUnary nUnary MNonempty) divrem

theorem natModFn_unary_all (M n : BHist) : UnaryHistory (natModFn M n) := by
  induction n with
  | Empty =>
      exact unary_empty
  | e0 _ =>
      exact unary_empty
  | e1 tail ih =>
      cases previous : natDivRemFn M tail with
      | mk q r =>
          by_cases boundary : BHist.e1 r = M
          · have stepEq :
                natDivRemFn M (BHist.e1 tail) = (BHist.e1 q, BHist.Empty) :=
              natDivRemFn_e1_boundary previous boundary
            unfold natModFn
            rw [stepEq]
            exact unary_empty
          · have stepEq :
                natDivRemFn M (BHist.e1 tail) = (q, BHist.e1 r) :=
              natDivRemFn_e1_inside previous boundary
            have previousModSame : hsame (natModFn M tail) r := by
              simp [natModFn, previous]
              rfl
            have rUnary : UnaryHistory r := unary_transport ih previousModSame
            unfold natModFn
            rw [stepEq]
            exact unary_e1_closed rUnary

theorem natModFn_strict_all {M n : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      NatUnaryStrictPrefix (natModFn M n) M := by
  intro MUnary MNonempty
  induction n with
  | Empty =>
      exact ⟨M, MUnary, MNonempty, cont_left_unit M⟩
  | e0 _ =>
      exact ⟨M, MUnary, MNonempty, cont_left_unit M⟩
  | e1 tail ih =>
      cases previous : natDivRemFn M tail with
      | mk q r =>
          by_cases boundary : BHist.e1 r = M
          · have stepEq :
                natDivRemFn M (BHist.e1 tail) = (BHist.e1 q, BHist.Empty) :=
              natDivRemFn_e1_boundary previous boundary
            unfold natModFn
            rw [stepEq]
            exact ⟨M, MUnary, MNonempty, cont_left_unit M⟩
          · have stepEq :
                natDivRemFn M (BHist.e1 tail) = (q, BHist.e1 r) :=
              natDivRemFn_e1_inside previous boundary
            have previousModSame : hsame (natModFn M tail) r := by
              simp [natModFn, previous]
              rfl
            have rUnary : UnaryHistory r := unary_transport (natModFn_unary_all M tail) previousModSame
            have rStrict : NatUnaryStrictPrefix r M := by
              exact NatUnaryStrictPrefix_hsame_source_transport_for_divides_closure ih previousModSame
            unfold natModFn
            rw [stepEq]
            exact NatUnaryStrictPrefix_succ_of_not_boundary MUnary rUnary rStrict boundary

def natMod (M n : BHist) : BHist :=
  natModFn M n

theorem natMod_unary (M n : BHist) : UnaryHistory (natMod M n) :=
  natModFn_unary_all M n

theorem natMod_strict {M n : BHist} :
    UnaryHistory M -> 0 < bwordLength M -> NatUnaryStrictPrefix (natMod M n) M := by
  intro MUnary MPositive
  have MNonempty : hsame M BHist.Empty -> False := by
    intro emptyM
    cases emptyM
    exact Nat.lt_irrefl 0 MPositive
  exact natModFn_strict_all MUnary MNonempty

theorem natModFn_rem_rem_of_dvd {M K n : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory K -> (hsame K BHist.Empty -> False) ->
        UnaryHistory n -> NatDivides M K ->
          hsame (natModFn M (natModFn K n)) (natModFn M n) := by
  intro MUnary MNonempty KUnary KNonempty nUnary dividesMK
  exact rem_rem_of_dvd MUnary MNonempty dividesMK
    (natModFn_spec KUnary nUnary KNonempty)
    (natModFn_spec MUnary nUnary MNonempty)
    (natModFn_spec MUnary
      (natModFn_unary KUnary nUnary KNonempty) MNonempty)

theorem natModFn_add_reduce_same_mod {M x y : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory x -> UnaryHistory y ->
        hsame (natModFn M (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)))
          (natModFn M (BEDC.FKernel.Cont.append x y)) := by
  intro MUnary MNonempty xUnary yUnary
  have divremX := natModFn_spec MUnary xUnary MNonempty
  have divremY := natModFn_spec MUnary yUnary MNonempty
  cases divremX with
  | intro mx dataX =>
      cases divremY with
      | intro my dataY =>
          have remXUnary : UnaryHistory (natModFn M x) :=
            NatAdd_right_unary dataX.right.left
          have remYUnary : UnaryHistory (natModFn M y) :=
            NatAdd_right_unary dataY.right.left
          have mxUnary : UnaryHistory mx :=
            NatMul_result_unary MUnary dataX.left
          have myUnary : UnaryHistory my :=
            NatMul_result_unary MUnary dataY.left
          have dividesMx : NatDivides M mx :=
            ⟨natQuotFn M x, NatMul_right_unary dataX.left, dataX.left⟩
          have dividesMy : NatDivides M my :=
            ⟨natQuotFn M y, NatMul_right_unary dataY.left, dataY.left⟩
          have dividesPrefix : NatDivides M (BEDC.FKernel.Cont.append mx my) :=
            NatDivides_cont_closed dividesMx dividesMy (cont_intro rfl)
          have displaySum :
              Cont (BEDC.FKernel.Cont.append mx my)
                (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)) (BEDC.FKernel.Cont.append x y) := by
            exact cont_intro
              (by
                calc
                  BEDC.FKernel.Cont.append x y =
                      BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx (natModFn M x)) y :=
                    congrArg (fun h => BEDC.FKernel.Cont.append h y) dataX.right.left.right.right
                  _ = BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx (natModFn M x))
                        (BEDC.FKernel.Cont.append my (natModFn M y)) :=
                    congrArg (fun h => BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx (natModFn M x)) h)
                      dataY.right.left.right.right
                  _ = BEDC.FKernel.Cont.append mx (BEDC.FKernel.Cont.append (natModFn M x)
                        (BEDC.FKernel.Cont.append my (natModFn M y))) :=
                    append_assoc mx (natModFn M x) (BEDC.FKernel.Cont.append my (natModFn M y))
                  _ = BEDC.FKernel.Cont.append mx (BEDC.FKernel.Cont.append my
                        (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y))) :=
                    congrArg (fun h => BEDC.FKernel.Cont.append mx h)
                      (by
                        calc
                          BEDC.FKernel.Cont.append (natModFn M x) (BEDC.FKernel.Cont.append my (natModFn M y)) =
                              BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append (natModFn M x) my) (natModFn M y) :=
                            (append_assoc (natModFn M x) my (natModFn M y)).symm
                          _ = BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append my (natModFn M x)) (natModFn M y) :=
                            congrArg (fun h => BEDC.FKernel.Cont.append h (natModFn M y))
                              (unary_append_comm remXUnary myUnary)
                          _ = BEDC.FKernel.Cont.append my (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)) :=
                            append_assoc my (natModFn M x) (natModFn M y))
                  _ = BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my)
                        (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)) :=
                    (append_assoc mx my
                      (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y))).symm)
          have remSumUnary :
              UnaryHistory (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)) :=
            unary_append_closed remXUnary remYUnary
          have nestedDivrem :=
            natModFn_spec MUnary remSumUnary MNonempty
          have directDivrem :=
            natModFn_spec MUnary (unary_append_closed xUnary yUnary) MNonempty
          cases dividesPrefix with
          | intro qPrefix qPrefixData =>
              cases nestedDivrem with
              | intro nestedProduct nestedData =>
                  have combinedMul :
                      NatMul M (BEDC.FKernel.Cont.append qPrefix
                        (natQuotFn M (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y))))
                        (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my) nestedProduct) :=
                    NatMul_append_cont qPrefixData.right nestedData.left (cont_intro rfl)
                  have combinedDisplay :
                      Cont (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my) nestedProduct)
                        (natModFn M (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)))
                        (BEDC.FKernel.Cont.append x y) := by
                    exact cont_intro
                      (by
                        calc
                          BEDC.FKernel.Cont.append x y =
                              BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my)
                                (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y)) :=
                            displaySum
                          _ = BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my)
                                (BEDC.FKernel.Cont.append nestedProduct
                                  (natModFn M (BEDC.FKernel.Cont.append (natModFn M x)
                                    (natModFn M y)))) :=
                            congrArg (fun h => BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my) h)
                              nestedData.right.left.right.right
                          _ = BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my) nestedProduct)
                                (natModFn M (BEDC.FKernel.Cont.append (natModFn M x)
                                  (natModFn M y))) :=
                            (append_assoc (BEDC.FKernel.Cont.append mx my) nestedProduct
                              (natModFn M (BEDC.FKernel.Cont.append (natModFn M x)
                                (natModFn M y)))).symm)
                  have synthetic :
                      NatDivRem M (BEDC.FKernel.Cont.append x y)
                        (BEDC.FKernel.Cont.append qPrefix
                          (natQuotFn M (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y))))
                        (natModFn M (BEDC.FKernel.Cont.append (natModFn M x) (natModFn M y))) :=
                    ⟨BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append mx my) nestedProduct, combinedMul,
                      And.intro
                        (NatMul_result_unary MUnary combinedMul)
                        (And.intro
                          (NatAdd_right_unary nestedData.right.left)
                          combinedDisplay),
                      nestedData.right.right⟩
                  exact (divRem_unique MUnary MNonempty synthetic directDivrem).right

theorem natModFn_append_hsame_transport {M a b c d : BHist} :
    hsame a b -> hsame c d ->
      hsame (natModFn M (BEDC.FKernel.Cont.append a c))
        (natModFn M (BEDC.FKernel.Cont.append b d)) := by
  intro sameA sameC
  cases sameA
  cases sameC
  rfl

theorem natModFn_hsame_arg_transport {M a b : BHist} :
    hsame a b -> hsame (natModFn M a) (natModFn M b) := by
  intro same
  cases same
  rfl

theorem mod_idem {M a : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory a ->
      hsame (natModFn M (natModFn M a)) (natModFn M a) := by
  intro MUnary MNonempty aUnary
  exact natModFn_rem_rem_of_dvd MUnary MNonempty MUnary MNonempty aUnary
    (NatDivides_reflexive_pair MUnary).right

theorem dvd_iff_mod_zero {M a : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory a ->
      (NatDivides M a ↔ hsame (natModFn M a) BHist.Empty) := by
  intro MUnary MNonempty aUnary
  exact dvd_iff_rem_zero MUnary MNonempty
    (natModFn_spec MUnary aUnary MNonempty)

theorem mod_add_compat {M a b : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b ->
        hsame (natModFn M (BEDC.FKernel.Cont.append a b))
          (natModFn M (BEDC.FKernel.Cont.append (natModFn M a) (natModFn M b))) := by
  intro MUnary MNonempty aUnary bUnary
  exact hsame_symm (natModFn_add_reduce_same_mod MUnary MNonempty aUnary bUnary)

theorem natModFn_add_congruence {M a b c d : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory c -> UnaryHistory b -> UnaryHistory d ->
        hsame (natModFn M a) (natModFn M b) ->
          hsame (natModFn M c) (natModFn M d) ->
            hsame (natModFn M (BEDC.FKernel.Cont.append a c))
              (natModFn M (BEDC.FKernel.Cont.append b d)) := by
  intro MUnary MNonempty aUnary cUnary bUnary dUnary sameA sameC
  have leftReduce :
      hsame (natModFn M (BEDC.FKernel.Cont.append a c))
        (natModFn M (BEDC.FKernel.Cont.append (natModFn M a) (natModFn M c))) :=
    mod_add_compat MUnary MNonempty aUnary cUnary
  have middle :
      hsame
        (natModFn M (BEDC.FKernel.Cont.append (natModFn M a) (natModFn M c)))
        (natModFn M (BEDC.FKernel.Cont.append (natModFn M b) (natModFn M d))) :=
    natModFn_append_hsame_transport sameA sameC
  have rightReduce :
      hsame
        (natModFn M (BEDC.FKernel.Cont.append (natModFn M b) (natModFn M d)))
        (natModFn M (BEDC.FKernel.Cont.append b d)) :=
    natModFn_add_reduce_same_mod MUnary MNonempty bUnary dUnary
  exact hsame_trans leftReduce (hsame_trans middle rightReduce)

theorem natMulFn_hsame_transport {a b c d : BHist} :
    hsame a b -> hsame c d -> hsame (natMulFn a c) (natMulFn b d) := by
  intro sameA sameC
  cases sameA
  cases sameC
  rfl

theorem natMulFn_comm_hsame {a b : BHist} :
    UnaryHistory a -> UnaryHistory b -> hsame (natMulFn a b) (natMulFn b a) := by
  intro aUnary bUnary
  exact NatMul_comm_hsame aUnary bUnary
    (natMulFn_rel aUnary bUnary) (natMulFn_rel bUnary aUnary)

theorem natModFn_mul_left_reduce_same_mod {M a b : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b ->
        hsame (natModFn M (natMulFn (natModFn M a) b))
          (natModFn M (natMulFn a b)) := by
  intro MUnary MNonempty aUnary bUnary
  induction b with
  | Empty =>
      rfl
  | e0 _ =>
      cases bUnary
  | e1 tail ih =>
      have tailUnary : UnaryHistory tail := unary_e1_inversion bUnary
      have ihTail :
          hsame (natModFn M (natMulFn (natModFn M a) tail))
            (natModFn M (natMulFn a tail)) :=
        ih tailUnary
      change
        hsame
          (natModFn M
            (BEDC.FKernel.Cont.append (natMulFn (natModFn M a) tail) (natModFn M a)))
          (natModFn M (BEDC.FKernel.Cont.append (natMulFn a tail) a))
      have remAUnary : UnaryHistory (natModFn M a) :=
        natModFn_unary MUnary aUnary MNonempty
      exact natModFn_add_congruence MUnary MNonempty
        (natMulFn_unary remAUnary tailUnary) remAUnary
        (natMulFn_unary aUnary tailUnary) aUnary
        ihTail (mod_idem MUnary MNonempty aUnary)

theorem natModFn_mul_right_reduce_same_mod {M a b : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b ->
        hsame (natModFn M (natMulFn a (natModFn M b)))
          (natModFn M (natMulFn a b)) := by
  intro MUnary MNonempty aUnary bUnary
  have remBUnary : UnaryHistory (natModFn M b) :=
    natModFn_unary MUnary bUnary MNonempty
  have leftComm :
      hsame (natModFn M (natMulFn a (natModFn M b)))
        (natModFn M (natMulFn (natModFn M b) a)) :=
    natModFn_hsame_arg_transport (M := M)
      (natMulFn_comm_hsame aUnary remBUnary)
  have reduceLeft :
      hsame (natModFn M (natMulFn (natModFn M b) a))
        (natModFn M (natMulFn b a)) :=
    natModFn_mul_left_reduce_same_mod MUnary MNonempty bUnary aUnary
  have rightComm :
      hsame (natModFn M (natMulFn b a))
        (natModFn M (natMulFn a b)) :=
    natModFn_hsame_arg_transport (M := M)
      (natMulFn_comm_hsame bUnary aUnary)
  exact hsame_trans leftComm (hsame_trans reduceLeft rightComm)

theorem mod_mul_compat {M a b : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b ->
        hsame (natModFn M (natMulFn a b))
          (natModFn M (natMulFn (natModFn M a) (natModFn M b))) := by
  intro MUnary MNonempty aUnary bUnary
  have remAUnary : UnaryHistory (natModFn M a) :=
    natModFn_unary MUnary aUnary MNonempty
  have reduceRight :
      hsame (natModFn M (natMulFn (natModFn M a) (natModFn M b)))
        (natModFn M (natMulFn (natModFn M a) b)) :=
    natModFn_mul_right_reduce_same_mod MUnary MNonempty remAUnary bUnary
  have reduceLeft :
      hsame (natModFn M (natMulFn (natModFn M a) b))
        (natModFn M (natMulFn a b)) :=
    natModFn_mul_left_reduce_same_mod MUnary MNonempty aUnary bUnary
  exact hsame_symm (hsame_trans reduceRight reduceLeft)

theorem natModFn_of_strict {M a : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> NatUnaryStrictPrefix a M -> hsame (natModFn M a) a := by
  intro MUnary MNonempty aUnary aStrict
  have displayed : NatDivRem M a BHist.Empty a :=
    ⟨BHist.Empty, NatMul.zero MUnary,
      And.intro unary_empty (And.intro aUnary (cont_left_unit a)),
      aStrict⟩
  exact (natModFn_unique MUnary aUnary MNonempty displayed).right

structure BoundedNat (M : BHist) where
  val : BHist
  isLt : NatUnaryStrictPrefix val M

theorem BoundedNat_unary {M : BHist} (MUnary : UnaryHistory M) (x : BoundedNat M) :
    UnaryHistory x.val := by
  cases x.isLt with
  | intro tail data =>
      exact unary_cont_left_factor data.right.right MUnary

def ZpTrunc (p N : BHist) : Type :=
  BoundedNat (pPowCanon p N)

def fromNatModPow (p N n : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N) :
    ZpTrunc p N :=
  { val := natMod (pPowCanon p N) n
    isLt := natMod_strict (pPowCanon_unary p N)
      (pPowCanon_positive_of_prime prime NUnary) }

def ZpEqTrunc {p N : BHist} (x y : ZpTrunc p N) : Prop :=
  hsame x.val y.val

def reduce (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x : ZpTrunc p (BHist.e1 N)) : ZpTrunc p N :=
  fromNatModPow p N x.val prime NUnary

theorem fromNatModPow_reduce_compat {p N n : BHist}
    (prime : NatPrime p) (NUnary : UnaryHistory N) (nUnary : UnaryHistory n) :
      ZpEqTrunc
        (reduce p N prime NUnary
          (fromNatModPow p (BHist.e1 N) n prime (unary_e1_closed NUnary)))
        (fromNatModPow p N n prime NUnary) := by
  unfold reduce fromNatModPow ZpEqTrunc natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have KUnary : UnaryHistory (pPowCanon p (BHist.e1 N)) :=
    pPowCanon_unary p (BHist.e1 N)
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NUnary
  have KNonempty : hsame (pPowCanon p (BHist.e1 N)) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime (unary_e1_closed NUnary)
  have pref : NatUnaryPrefix N (BHist.e1 N) :=
    ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, cont_intro rfl⟩
  have dividesMK : NatDivides (pPowCanon p N) (pPowCanon p (BHist.e1 N)) :=
    pow_dvd_pow_of_le prime NUnary (unary_e1_closed NUnary) pref
  exact natModFn_rem_rem_of_dvd MUnary MNonempty KUnary KNonempty nUnary dividesMK

def ZpCompatible (p : BHist) (prime : NatPrime p)
    (trunc : (N : BHist) -> UnaryHistory N -> ZpTrunc p N) : Prop :=
  ∀ (N : BHist) (NUnary : UnaryHistory N),
    ZpEqTrunc (reduce p N prime NUnary
      (trunc (BHist.e1 N) (unary_e1_closed NUnary))) (trunc N NUnary)

structure ZpInt (p : BHist) where
  prime : NatPrime p
  trunc : (N : BHist) -> UnaryHistory N -> ZpTrunc p N
  compat : ZpCompatible p prime trunc

def ZpEq {p : BHist} (x y : ZpInt p) : Prop :=
  ∀ (N : BHist) (NUnary : UnaryHistory N),
    hsame (x.trunc N NUnary).val (y.trunc N NUnary).val

theorem natToZp_compat (p n : BHist) (prime : NatPrime p) (nUnary : UnaryHistory n) :
    ZpCompatible p prime (fun N NUnary => fromNatModPow p N n prime NUnary) := by
  intro N NUnary
  exact fromNatModPow_reduce_compat prime NUnary nUnary

def natToZp (p : BHist) (prime : NatPrime p) (n : BHist) (nUnary : UnaryHistory n) : ZpInt p :=
  { prime := prime
    trunc := fun N NUnary => fromNatModPow p N n prime NUnary
    compat := natToZp_compat p n prime nUnary }

def zpZero (p : BHist) (prime : NatPrime p) : ZpInt p :=
  natToZp p prime BHist.Empty unary_empty

def zpOne (p : BHist) (prime : NatPrime p) : ZpInt p :=
  natToZp p prime NatOne (unary_e1_closed unary_empty)

def fromIntModPow (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x : BHist × BHist) : ZpTrunc p N :=
  fromNatModPow p N (BEDC.FKernel.Cont.append x.1 (natMod (pPowCanon p N) x.2))
    prime NUnary

theorem fromIntModPow_compat (p : BHist) (prime : NatPrime p)
    (x : BHist × BHist) (xCarrier : IntPairCarrier x.1 x.2) :
      ZpCompatible p prime (fun N NUnary => fromIntModPow p N prime NUnary x) := by
  intro N NUnary
  unfold reduce fromIntModPow fromNatModPow ZpEqTrunc natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have KUnary : UnaryHistory (pPowCanon p (BHist.e1 N)) :=
    pPowCanon_unary p (BHist.e1 N)
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NUnary
  have KNonempty : hsame (pPowCanon p (BHist.e1 N)) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime (unary_e1_closed NUnary)
  have pref : NatUnaryPrefix N (BHist.e1 N) :=
    ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, cont_intro rfl⟩
  have dividesMK : NatDivides (pPowCanon p N) (pPowCanon p (BHist.e1 N)) :=
    pow_dvd_pow_of_le prime NUnary (unary_e1_closed NUnary) pref
  have negKUnary : UnaryHistory (natModFn (pPowCanon p (BHist.e1 N)) x.2) :=
    natModFn_unary KUnary xCarrier.right KNonempty
  have leftDrop :
      hsame
        (natModFn (pPowCanon p N)
          (natModFn (pPowCanon p (BHist.e1 N))
            (BEDC.FKernel.Cont.append x.1
              (natModFn (pPowCanon p (BHist.e1 N)) x.2))))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append x.1
            (natModFn (pPowCanon p (BHist.e1 N)) x.2))) :=
    natModFn_rem_rem_of_dvd MUnary MNonempty KUnary KNonempty
      (unary_append_closed xCarrier.left negKUnary) dividesMK
  have negRem :
      hsame
        (natModFn (pPowCanon p N)
          (natModFn (pPowCanon p (BHist.e1 N)) x.2))
        (natModFn (pPowCanon p N) x.2) :=
    natModFn_rem_rem_of_dvd MUnary MNonempty KUnary KNonempty xCarrier.right dividesMK
  have stepA :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append x.1
            (natModFn (pPowCanon p (BHist.e1 N)) x.2)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N) x.1)
            (natModFn (pPowCanon p N)
              (natModFn (pPowCanon p (BHist.e1 N)) x.2)))) := by
    exact hsame_symm
      (natModFn_add_reduce_same_mod MUnary MNonempty xCarrier.left negKUnary)
  have stepB :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N) x.1)
            (natModFn (pPowCanon p N)
              (natModFn (pPowCanon p (BHist.e1 N)) x.2))))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N) x.1)
            (natModFn (pPowCanon p N) x.2))) :=
    natModFn_append_hsame_transport (hsame_refl _) negRem
  have negSelf :
      hsame
        (natModFn (pPowCanon p N) (natModFn (pPowCanon p N) x.2))
        (natModFn (pPowCanon p N) x.2) :=
    natModFn_rem_rem_of_dvd MUnary MNonempty MUnary MNonempty xCarrier.right
      (NatDivides_reflexive_pair MUnary).right
  have stepC :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N) x.1)
            (natModFn (pPowCanon p N) x.2)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append x.1 (natModFn (pPowCanon p N) x.2))) := by
    have raw :=
      natModFn_add_reduce_same_mod MUnary MNonempty xCarrier.left
        (natModFn_unary MUnary xCarrier.right MNonempty)
    have rawLeftTransport :
        hsame
          (natModFn (pPowCanon p N)
            (BEDC.FKernel.Cont.append
              (natModFn (pPowCanon p N) x.1)
              (natModFn (pPowCanon p N) x.2)))
          (natModFn (pPowCanon p N)
            (BEDC.FKernel.Cont.append
              (natModFn (pPowCanon p N) x.1)
              (natModFn (pPowCanon p N)
                (natModFn (pPowCanon p N) x.2)))) :=
      natModFn_append_hsame_transport (hsame_refl _) (hsame_symm negSelf)
    exact hsame_trans rawLeftTransport raw
  exact hsame_trans leftDrop (hsame_trans stepA (hsame_trans stepB stepC))

def intPairToZp (p : BHist) (prime : NatPrime p) (x : BHist × BHist)
    (compat :
      ZpCompatible p prime (fun N NUnary => fromIntModPow p N prime NUnary x)) : ZpInt p :=
  { prime := prime
    trunc := fun N NUnary => fromIntModPow p N prime NUnary x
    compat := compat }

def intToZp (p : BHist) (prime : NatPrime p)
    (x : BHist × BHist) (xCarrier : IntPairCarrier x.1 x.2) : ZpInt p :=
  { prime := prime
    trunc := fun N NUnary => fromIntModPow p N prime NUnary x
    compat := fromIntModPow_compat p prime x xCarrier }

def zpAddTrunc (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x y : ZpTrunc p N) : ZpTrunc p N :=
  fromNatModPow p N (BEDC.FKernel.Cont.append x.val y.val) prime NUnary

theorem zpAdd_compat (p : BHist) (x y : ZpInt p) :
    ZpCompatible p x.prime
      (fun N NUnary => zpAddTrunc p N x.prime NUnary (x.trunc N NUnary) (y.trunc N NUnary)) := by
  intro N NUnary
  unfold reduce zpAddTrunc fromNatModPow ZpEqTrunc natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have KUnary : UnaryHistory (pPowCanon p (BHist.e1 N)) :=
    pPowCanon_unary p (BHist.e1 N)
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have KNonempty : hsame (pPowCanon p (BHist.e1 N)) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime (unary_e1_closed NUnary)
  have xNextUnary : UnaryHistory (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val :=
    BoundedNat_unary KUnary (x.trunc (BHist.e1 N) (unary_e1_closed NUnary))
  have yNextUnary : UnaryHistory (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val :=
    BoundedNat_unary KUnary (y.trunc (BHist.e1 N) (unary_e1_closed NUnary))
  have pref : NatUnaryPrefix N (BHist.e1 N) :=
    ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, cont_intro rfl⟩
  have dividesMK : NatDivides (pPowCanon p N) (pPowCanon p (BHist.e1 N)) :=
    pow_dvd_pow_of_le x.prime NUnary (unary_e1_closed NUnary) pref
  have xCompat := x.compat N NUnary
  have yCompat := y.compat N NUnary
  unfold reduce fromNatModPow ZpEqTrunc natMod at xCompat yCompat
  have outerRem :
      hsame
        (natModFn (pPowCanon p N)
          (natModFn (pPowCanon p (BHist.e1 N))
            (BEDC.FKernel.Cont.append
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
              (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
            (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)) := by
    exact natModFn_rem_rem_of_dvd MUnary MNonempty KUnary KNonempty
      (unary_append_closed xNextUnary yNextUnary) dividesMK
  have reduceNextSum :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
            (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)
            (natModFn (pPowCanon p N)
              (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val))) := by
    exact hsame_symm (natModFn_add_reduce_same_mod MUnary MNonempty xNextUnary yNextUnary)
  have compatTransport :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)
            (natModFn (pPowCanon p N)
              (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (x.trunc N NUnary).val
            (y.trunc N NUnary).val)) := by
    exact natModFn_append_hsame_transport xCompat yCompat
  change hsame
    (natModFn (pPowCanon p N)
      (natModFn (pPowCanon p (BHist.e1 N))
        (BEDC.FKernel.Cont.append
          (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
          (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
  exact hsame_trans outerRem
    (hsame_trans reduceNextSum
      compatTransport)

def zpAdd (p : BHist) (x y : ZpInt p) : ZpInt p :=
  { prime := x.prime
    trunc := fun N NUnary => zpAddTrunc p N x.prime NUnary (x.trunc N NUnary) (y.trunc N NUnary)
    compat := zpAdd_compat p x y }

def zpMulTrunc (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x y : ZpTrunc p N) : ZpTrunc p N :=
  fromNatModPow p N (natMulFn x.val y.val) prime NUnary

theorem zpMul_compat (p : BHist) (x y : ZpInt p) :
    ZpCompatible p x.prime
      (fun N NUnary => zpMulTrunc p N x.prime NUnary (x.trunc N NUnary) (y.trunc N NUnary)) := by
  intro N NUnary
  unfold reduce zpMulTrunc fromNatModPow ZpEqTrunc natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have KUnary : UnaryHistory (pPowCanon p (BHist.e1 N)) :=
    pPowCanon_unary p (BHist.e1 N)
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have KNonempty : hsame (pPowCanon p (BHist.e1 N)) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime (unary_e1_closed NUnary)
  have xNextUnary : UnaryHistory (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val :=
    BoundedNat_unary KUnary (x.trunc (BHist.e1 N) (unary_e1_closed NUnary))
  have yNextUnary : UnaryHistory (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val :=
    BoundedNat_unary KUnary (y.trunc (BHist.e1 N) (unary_e1_closed NUnary))
  have pref : NatUnaryPrefix N (BHist.e1 N) :=
    ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, cont_intro rfl⟩
  have dividesMK : NatDivides (pPowCanon p N) (pPowCanon p (BHist.e1 N)) :=
    pow_dvd_pow_of_le x.prime NUnary (unary_e1_closed NUnary) pref
  have xCompat := x.compat N NUnary
  have yCompat := y.compat N NUnary
  unfold reduce fromNatModPow ZpEqTrunc natMod at xCompat yCompat
  have outerRem :
      hsame
        (natModFn (pPowCanon p N)
          (natModFn (pPowCanon p (BHist.e1 N))
            (natMulFn
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
              (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
        (natModFn (pPowCanon p N)
          (natMulFn
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
            (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)) := by
    exact natModFn_rem_rem_of_dvd MUnary MNonempty KUnary KNonempty
      (natMulFn_unary xNextUnary yNextUnary) dividesMK
  have reduceNextProduct :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
            (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val))
        (natModFn (pPowCanon p N)
          (natMulFn
            (natModFn (pPowCanon p N)
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)
            (natModFn (pPowCanon p N)
              (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val))) := by
    exact mod_mul_compat MUnary MNonempty xNextUnary yNextUnary
  have compatTransport :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (natModFn (pPowCanon p N)
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)
            (natModFn (pPowCanon p N)
              (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)) :=
    natModFn_hsame_arg_transport (M := pPowCanon p N)
      (natMulFn_hsame_transport xCompat yCompat)
  change hsame
    (natModFn (pPowCanon p N)
      (natModFn (pPowCanon p (BHist.e1 N))
        (natMulFn
          (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val
          (y.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
    (natModFn (pPowCanon p N)
      (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
  exact hsame_trans outerRem
    (hsame_trans reduceNextProduct compatTransport)

def zpMul (p : BHist) (x y : ZpInt p) : ZpInt p :=
  { prime := x.prime
    trunc := fun N NUnary => zpMulTrunc p N x.prime NUnary (x.trunc N NUnary) (y.trunc N NUnary)
    compat := zpMul_compat p x y }

theorem ZpEq_refl {p : BHist} (x : ZpInt p) : ZpEq x x := by
  intro N NUnary
  exact hsame_refl _

theorem ZpEq_symm {p : BHist} {x y : ZpInt p} :
    ZpEq x y -> ZpEq y x := by
  intro same N NUnary
  exact hsame_symm (same N NUnary)

theorem ZpEq_trans {p : BHist} {x y z : ZpInt p} :
    ZpEq x y -> ZpEq y z -> ZpEq x z := by
  intro sameXY sameYZ N NUnary
  exact hsame_trans (sameXY N NUnary) (sameYZ N NUnary)

theorem zpAdd_comm (p : BHist) (x y : ZpInt p) :
    ZpEq (zpAdd p x y) (zpAdd p y x) := by
  intro N NUnary
  unfold zpAdd zpAddTrunc fromNatModPow natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  exact natModFn_hsame_arg_transport (M := pPowCanon p N)
    (unary_append_comm xUnary yUnary)

theorem zpMul_comm (p : BHist) (x y : ZpInt p) :
    ZpEq (zpMul p x y) (zpMul p y x) := by
  intro N NUnary
  unfold zpMul zpMulTrunc fromNatModPow natMod
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  exact natModFn_hsame_arg_transport (M := pPowCanon p N)
    (natMulFn_comm_hsame xUnary yUnary)

theorem zpZero_add_left (p : BHist) (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpAdd p (zpZero p prime) x) x := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N) BHist.Empty) (x.trunc N NUnary).val))
    (x.trunc N NUnary).val
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NUnary
  have xStrict : NatUnaryStrictPrefix (x.trunc N NUnary).val (pPowCanon p N) :=
    (x.trunc N NUnary).isLt
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have leftEmpty :
      hsame (natModFn (pPowCanon p N) BHist.Empty) BHist.Empty := by
    rfl
  have raw :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N) BHist.Empty) (x.trunc N NUnary).val))
        (natModFn (pPowCanon p N) (x.trunc N NUnary).val) := by
    cases leftEmpty
    exact natModFn_hsame_arg_transport (M := pPowCanon p N)
      (append_empty_left (x.trunc N NUnary).val)
  exact hsame_trans raw (natModFn_of_strict MUnary MNonempty xUnary xStrict)

theorem zpZero_add_right (p : BHist) (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpAdd p x (zpZero p prime)) x := by
  exact ZpEq_trans (zpAdd_comm p x (zpZero p prime))
    (zpZero_add_left p prime x)

theorem zpAdd_assoc (p : BHist) (x y z : ZpInt p) :
    ZpEq (zpAdd p (zpAdd p x y) z) (zpAdd p x (zpAdd p y z)) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
        (z.trunc N NUnary).val))
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (x.trunc N NUnary).val
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))))
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have zUnary : UnaryHistory (z.trunc N NUnary).val :=
    BoundedNat_unary MUnary (z.trunc N NUnary)
  have xyUnary :
      UnaryHistory (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    unary_append_closed xUnary yUnary
  have yzUnary :
      UnaryHistory (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val) :=
    unary_append_closed yUnary zUnary
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val)) := by
    exact hsame_symm
      (natModFn_add_congruence MUnary MNonempty
        xyUnary zUnary
        (natModFn_unary MUnary xyUnary MNonempty) zUnary
        (hsame_symm (mod_idem MUnary MNonempty xyUnary)) (hsame_refl _))
  have rawAssoc :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (x.trunc N NUnary).val
            (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_hsame_arg_transport (M := pPowCanon p N)
      (BEDC.FKernel.Cont.append_assoc
        (x.trunc N NUnary).val (y.trunc N NUnary).val (z.trunc N NUnary).val)
  have rawToRight :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (x.trunc N NUnary).val
            (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (x.trunc N NUnary).val
            (natModFn (pPowCanon p N)
              (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val)))) := by
    exact natModFn_add_congruence MUnary MNonempty
      xUnary yzUnary xUnary (natModFn_unary MUnary yzUnary MNonempty)
      (hsame_refl _) (hsame_symm (mod_idem MUnary MNonempty yzUnary))
  exact hsame_trans leftToRaw (hsame_trans rawAssoc rawToRight)

theorem zpOne_mul_left (p : BHist) (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpMul p (zpOne p prime) x) x := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn (natModFn (pPowCanon p N) NatOne) (x.trunc N NUnary).val))
    (x.trunc N NUnary).val
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have xStrict : NatUnaryStrictPrefix (x.trunc N NUnary).val (pPowCanon p N) :=
    (x.trunc N NUnary).isLt
  have productReduce :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn (natModFn (pPowCanon p N) NatOne) (x.trunc N NUnary).val))
        (natModFn (pPowCanon p N) (natMulFn NatOne (x.trunc N NUnary).val)) :=
    natModFn_mul_left_reduce_same_mod MUnary MNonempty
      (unary_e1_closed unary_empty) xUnary
  have productUnit :
      hsame
        (natModFn (pPowCanon p N) (natMulFn NatOne (x.trunc N NUnary).val))
        (natModFn (pPowCanon p N) (x.trunc N NUnary).val) :=
    natModFn_hsame_arg_transport (M := pPowCanon p N)
      (NatMul_unit_left_hsame xUnary
        (natMulFn_rel (unary_e1_closed unary_empty) xUnary))
  exact hsame_trans productReduce
    (hsame_trans productUnit (natModFn_of_strict MUnary MNonempty xUnary xStrict))

theorem zpOne_mul_right (p : BHist) (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpMul p x (zpOne p prime)) x := by
  exact ZpEq_trans (zpMul_comm p x (zpOne p prime))
    (zpOne_mul_left p prime x)

theorem zpMul_assoc (p : BHist) (x y z : ZpInt p) :
    ZpEq (zpMul p (zpMul p x y) z) (zpMul p x (zpMul p y z)) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
        (z.trunc N NUnary).val))
    (natModFn (pPowCanon p N)
      (natMulFn
        (x.trunc N NUnary).val
        (natModFn (pPowCanon p N)
          (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val))))
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have zUnary : UnaryHistory (z.trunc N NUnary).val :=
    BoundedNat_unary MUnary (z.trunc N NUnary)
  have xyUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    natMulFn_unary xUnary yUnary
  have yzUnary : UnaryHistory (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary yUnary zUnary
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val)) :=
    natModFn_mul_left_reduce_same_mod MUnary MNonempty xyUnary zUnary
  have rawAssoc :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn
            (x.trunc N NUnary).val
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val))) := by
    have assocSame :
        hsame
          (natMulFn
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val)
          (natMulFn
            (x.trunc N NUnary).val
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)) :=
      NatMul_assoc_hsame xUnary yUnary zUnary
        (natMulFn_rel xUnary yUnary)
        (natMulFn_rel xyUnary zUnary)
        (natMulFn_rel yUnary zUnary)
        (natMulFn_rel xUnary yzUnary)
    exact natModFn_hsame_arg_transport (M := pPowCanon p N) assocSame
  have rawToRight :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (x.trunc N NUnary).val
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (natMulFn
            (x.trunc N NUnary).val
            (natModFn (pPowCanon p N)
              (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)))) := by
    exact hsame_symm
      (natModFn_mul_right_reduce_same_mod MUnary MNonempty xUnary yzUnary)
  exact hsame_trans leftToRaw (hsame_trans rawAssoc rawToRight)

def intSub (x y : BHist × BHist) : BHist × BHist :=
  BEDC.Derived.IntUp.intSub x y

theorem intSub_pair_carrier {x y : BHist × BHist} :
    IntPairCarrier x.1 x.2 -> IntPairCarrier y.1 y.2 ->
      IntPairCarrier (intSub x y).1 (intSub x y).2 := by
  intro hx hy
  exact BEDC.Derived.IntUp.intSub_carrier hx hy

def natDistanceInt (x y : BHist) : BMark × BHist :=
  if bwordLength y ≤ bwordLength x then
    (BMark.b0, zpuNatToUnary (bwordLength x - bwordLength y))
  else
    (BMark.b1, zpuNatToUnary (bwordLength y - bwordLength x))

theorem natDistanceInt_carrier (x y : BHist) :
    IntCarrier (natDistanceInt x y).1 (natDistanceInt x y).2 := by
  unfold natDistanceInt
  split
  · exact ⟨Or.inl rfl, zpuNatToUnary_unary _⟩
  · exact ⟨Or.inr rfl, zpuNatToUnary_unary _⟩

def Ball (p N x y : BHist) : Prop :=
  PDvdInt p N (natDistanceInt x y)

theorem same_residue_iff_ball {p N x y : BHist} :
    NatPrime p -> UnaryHistory N ->
      (hsame (natModFn (pPowCanon p N) (natDistanceInt x y).2) BHist.Empty ↔
        Ball p N x y) := by
  intro prime NUnary
  unfold Ball
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NUnary
  have magnitudeUnary : UnaryHistory (natDistanceInt x y).2 :=
    (natDistanceInt_carrier x y).right
  have powCanon : PPow p N (pPowCanon p N) :=
    pPowCanon_PPow prime.left NUnary
  constructor
  · intro remZero
    have dividesMagnitude : NatDivides (pPowCanon p N) (natDistanceInt x y).2 :=
      (dvd_iff_mod_zero MUnary MNonempty magnitudeUnary).mpr remZero
    exact And.intro (natDistanceInt_carrier x y)
      (Exists.intro (pPowCanon p N) (And.intro powCanon dividesMagnitude))
  · intro padicDivides
    cases padicDivides.right with
    | intro pk pkData =>
        have samePower : hsame pk (pPowCanon p N) :=
          PPow_functional pkData.left powCanon
        have dividesMagnitude : NatDivides (pPowCanon p N) (natDistanceInt x y).2 :=
          (NatDivides_divisor_hsame_transport pkData.right samePower).right
        exact (dvd_iff_mod_zero MUnary MNonempty magnitudeUnary).mp dividesMagnitude

theorem Ball_carrier {p N x y : BHist} :
    Ball p N x y -> IntCarrier (natDistanceInt x y).1 (natDistanceInt x y).2 := by
  intro ball
  exact ball.left

theorem natDistanceInt_magnitude_unary (x y : BHist) :
    UnaryHistory (natDistanceInt x y).2 :=
  (natDistanceInt_carrier x y).right

end BEDC.Derived.PadicUp
