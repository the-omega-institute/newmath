import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp
import BEDC.Derived.PrimeUp.NatMulTransport
import BEDC.Derived.PrimeUp.PrimeShape
import BEDC.Derived.PrimeUp.ResultBoundary

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

abbrev NatDvd (d n : BHist) : Prop :=
  NatDivides d n

def NatDivRem (M n q r : BHist) : Prop :=
  ∃ mq : BHist, NatMul M q mq ∧ NatAdd mq r n ∧ NatUnaryStrictPrefix r M

theorem NatDivRem_remainder_unary {M n q r : BHist} :
    NatDivRem M n q r -> UnaryHistory r := by
  intro divrem
  cases divrem with
  | intro _mq data =>
      exact NatAdd_right_unary data.right.left

theorem NatDivRem_divisor_unary {M n q r : BHist} :
    NatDivRem M n q r -> UnaryHistory M := by
  intro divrem
  cases divrem with
  | intro _mq data =>
      exact NatMul_left_unary data.left

theorem NatDivRem_dividend_unary {M n q r : BHist} :
    NatDivRem M n q r -> UnaryHistory n := by
  intro divrem
  cases divrem with
  | intro _mq data =>
      exact NatAdd_result_unary data.right.left

theorem NatDivRem_quotient_unary {M n q r : BHist} :
    NatDivRem M n q r -> UnaryHistory q := by
  intro divrem
  cases divrem with
  | intro _mq data =>
      exact NatMul_right_unary data.left

theorem NatDivRem_product_divides {M n q r : BHist} :
    NatDivRem M n q r -> ∃ mq : BHist, NatDivides M mq ∧ NatAdd mq r n := by
  intro divrem
  cases divrem with
  | intro mq data =>
      exact ⟨mq, ⟨q, NatMul_right_unary data.left, data.left⟩, data.right.left⟩

private theorem NatUnaryStrictPrefix_successor_gap_absurd {r t : BHist} :
    NatUnaryStrictPrefix r t -> NatUnaryStrictPrefix t (BHist.e1 r) -> False := by
  intro left right
  cases left with
  | intro leftTail leftData =>
      cases leftData with
      | intro leftUnary leftRest =>
          cases leftRest with
          | intro leftNonempty leftCont =>
              cases right with
              | intro rightTail rightData =>
                  cases rightData with
                  | intro rightUnary rightRest =>
                      cases rightRest with
                      | intro rightNonempty rightCont =>
                          have composite : Cont r (append leftTail rightTail) (BHist.e1 r) := by
                            exact cont_intro
                              (rightCont.trans
                                ((congrArg (fun y => append y rightTail) leftCont).trans
                                  (append_assoc r leftTail rightTail)))
                          have direct : Cont r (BHist.e1 BHist.Empty) (BHist.e1 r) :=
                            cont_intro rfl
                          have tailSame :
                              hsame (append leftTail rightTail) (BHist.e1 BHist.Empty) :=
                            cont_left_cancel composite direct
                          cases leftTail with
                          | Empty =>
                              exact leftNonempty rfl
                          | e0 leftTail =>
                              cases leftUnary
                          | e1 leftTail =>
                              cases rightTail with
                              | Empty =>
                                  exact rightNonempty rfl
                              | e0 rightTail =>
                                  cases rightUnary
                              | e1 rightTail =>
                                  have innerEmpty :
                                      hsame (append (BHist.e1 leftTail) rightTail) BHist.Empty :=
                                    BHist.e1.inj tailSame
                                  exact not_hsame_e1_empty
                                    (append_eq_empty_iff.mp innerEmpty).left

theorem NatMul_division_with_remainder {t x : BHist} :
    UnaryHistory t -> UnaryHistory x -> (hsame t BHist.Empty -> False) ->
      exists q r w : BHist,
        UnaryHistory q ∧ UnaryHistory r ∧ UnaryHistory w ∧ NatMul t q w ∧ Cont w r x ∧
          (hsame r BHist.Empty ∨ NatUnaryStrictPrefix r t) := by
  intro tUnary xUnary tNonempty
  induction x with
  | Empty =>
      exact ⟨BHist.Empty, BHist.Empty, BHist.Empty, unary_empty, unary_empty, unary_empty,
        NatMul.zero tUnary, cont_right_unit BHist.Empty, Or.inl rfl⟩
  | e0 x =>
      cases xUnary
  | e1 x ih =>
      have xTailUnary : UnaryHistory x := unary_e1_inversion xUnary
      cases ih xTailUnary with
      | intro q qRest =>
          cases qRest with
          | intro r rRest =>
              cases rRest with
              | intro w data =>
                  cases data with
                  | intro qUnary data =>
                      cases data with
                      | intro rUnary data =>
                          cases data with
                          | intro wUnary data =>
                              cases data with
                              | intro mul data =>
                                  cases data with
                                  | intro displayed remainderBound =>
                                      have nextRUnary : UnaryHistory (BHist.e1 r) :=
                                        unary_e1_closed rUnary
                                      have nextDisplayed :
                                          Cont w (BHist.e1 r) (BHist.e1 x) := by
                                        cases displayed
                                        rfl
                                      have total := NatUnaryPrefix_total nextRUnary tUnary
                                      cases total with
                                      | inl nextPrefix =>
                                          cases nextPrefix with
                                          | intro tail tailData =>
                                              cases NatUnaryPrefix_cont_tail_cases
                                                  tailData.left tailData.right with
                                              | inl nextSame =>
                                                  have step :
                                                      Cont w t (BHist.e1 x) :=
                                                    cont_hsame_transport (hsame_refl w)
                                                      nextSame (hsame_refl (BHist.e1 x))
                                                      nextDisplayed
                                                  exact
                                                    ⟨BHist.e1 q, BHist.Empty, BHist.e1 x,
                                                      unary_e1_closed qUnary, unary_empty,
                                                      xUnary, NatMul.succ mul step,
                                                      cont_right_unit (BHist.e1 x), Or.inl rfl⟩
                                              | inr nextStrict =>
                                                  exact
                                                    ⟨q, BHist.e1 r, w, qUnary, nextRUnary,
                                                      wUnary, mul, nextDisplayed,
                                                      Or.inr nextStrict⟩
                                      | inr tPrefix =>
                                          cases tPrefix with
                                          | intro tail tailData =>
                                              cases NatUnaryPrefix_cont_tail_cases
                                                  tailData.left tailData.right with
                                              | inl sameTNext =>
                                                  have step :
                                                      Cont w t (BHist.e1 x) :=
                                                    cont_hsame_transport (hsame_refl w)
                                                      (hsame_symm sameTNext)
                                                      (hsame_refl (BHist.e1 x)) nextDisplayed
                                                  exact
                                                    ⟨BHist.e1 q, BHist.Empty, BHist.e1 x,
                                                      unary_e1_closed qUnary, unary_empty,
                                                      xUnary, NatMul.succ mul step,
                                                      cont_right_unit (BHist.e1 x), Or.inl rfl⟩
                                              | inr overshoot =>
                                                  have baseStrict : NatUnaryStrictPrefix r t := by
                                                    cases remainderBound with
                                                    | inl rEmpty =>
                                                        cases rEmpty
                                                        exact ⟨t, tUnary, tNonempty,
                                                          cont_left_unit t⟩
                                                    | inr strict =>
                                                        exact strict
                                                  exact False.elim
                                                    (NatUnaryStrictPrefix_successor_gap_absurd
                                                      baseStrict overshoot)

theorem zero_or_succ_boundary {r M : BHist} :
    UnaryHistory M -> UnaryHistory r -> NatUnaryStrictPrefix r M ->
      (NatUnaryStrictPrefix (BHist.e1 r) M -> False) ->
        hsame (BHist.e1 r) M := by
  intro MUnary rUnary rLtM nextNotLt
  have nextUnary : UnaryHistory (BHist.e1 r) := unary_e1_closed rUnary
  have total := NatUnaryPrefix_total nextUnary MUnary
  cases total with
  | inl nextPrefix =>
      cases nextPrefix with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl sameNextM =>
              exact sameNextM
          | inr nextLtM =>
              exact False.elim (nextNotLt nextLtM)
  | inr MPrefix =>
      cases MPrefix with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl sameMNext =>
              exact hsame_symm sameMNext
          | inr MLtNext =>
              exact False.elim (NatUnaryStrictPrefix_successor_gap_absurd rLtM MLtNext)

theorem divRem_exists {M n : BHist} :
    UnaryHistory M -> UnaryHistory n -> (hsame M BHist.Empty -> False) ->
      ∃ q : BHist, ∃ r : BHist, NatDivRem M n q r := by
  intro MUnary nUnary MNonempty
  have raw := NatMul_division_with_remainder MUnary nUnary MNonempty
  cases raw with
  | intro q qRest =>
      cases qRest with
      | intro r rRest =>
          cases rRest with
          | intro mq data =>
              cases data with
              | intro qUnary data =>
                  cases data with
                  | intro rUnary data =>
                      cases data with
                      | intro mqUnary data =>
                          cases data with
                          | intro mul data =>
                              cases data with
                              | intro displayed remainderBound =>
                                  have strictR : NatUnaryStrictPrefix r M := by
                                    cases remainderBound with
                                    | inl rEmpty =>
                                        cases rEmpty
                                        exact ⟨M, MUnary, MNonempty, cont_left_unit M⟩
                                    | inr strict =>
                                        exact strict
                                  exact
                                    ⟨q, r, mq, mul,
                                      And.intro mqUnary (And.intro rUnary displayed), strictR⟩

theorem dvd_tail_of_dvd_sum {p x y z : BHist} :
    UnaryHistory p -> (hsame p BHist.Empty -> False) -> NatAdd x y z ->
      NatDivides p x -> NatDivides p z -> NatDivides p y := by
  intro pUnary pNonempty add dividesX dividesZ
  exact NatDivides_prefix_cancellation pUnary pNonempty add.left add.right.left
    (NatAdd_result_unary add) add.right.right dividesX dividesZ

theorem not_dvd_of_pos_lt {p r : BHist} :
    UnaryHistory p -> UnaryHistory r -> NatUnaryStrictPrefix (BHist.e1 BHist.Empty) p ->
      NatUnaryStrictPrefix BHist.Empty r -> NatUnaryStrictPrefix r p ->
        NatDivides p r -> False := by
  intro pUnary rUnary _pBeyondUnit rPositive rLtP divides
  have rNonempty : hsame r BHist.Empty -> False := by
    intro rEmpty
    cases rEmpty
    exact NatUnaryStrictPrefix_empty_right_absurd rPositive
  have boundary := NatDivides_nonempty_result_boundary divides rUnary rNonempty
  cases boundary with
  | inl samePR =>
      cases rLtP with
      | intro tail data =>
          exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
            (h := r) (k := p) (tail := tail)
            data.left data.right.left data.right.right (hsame_symm samePR)
  | inr pLtR =>
      exact NatUnaryStrictPrefix_asymm pLtR rLtP

theorem prime_no_proper_divisor {p a : BHist} :
    NatPrime p -> UnaryHistory a -> NatUnaryStrictPrefix (BHist.e1 BHist.Empty) a ->
      NatUnaryStrictPrefix a p -> NatDivides a p -> False := by
  intro prime aUnary unitLtA aLtP divides
  exact NatPrime_NatDivides_strict_between_absurd prime aUnary divides unitLtA aLtP

theorem dvd_iff_rem_zero {M n q r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> NatDivRem M n q r ->
      (NatDivides M n ↔ hsame r BHist.Empty) := by
  intro MUnary MNonempty divrem
  constructor
  · intro dividesN
    cases divrem with
    | intro mq data =>
        have dividesMq : NatDivides M mq := ⟨q, NatMul_right_unary data.left, data.left⟩
        have dividesR : NatDivides M r :=
          dvd_tail_of_dvd_sum MUnary MNonempty data.right.left dividesMq dividesN
        cases r with
        | Empty =>
            rfl
        | e0 rTail =>
            cases NatAdd_right_unary data.right.left
        | e1 rTail =>
            have rUnary : UnaryHistory (BHist.e1 rTail) := NatAdd_right_unary data.right.left
            have rNonempty : hsame (BHist.e1 rTail) BHist.Empty -> False := by
              intro same
              exact not_hsame_e1_empty same
            have boundary :=
              NatDivides_nonempty_result_boundary dividesR rUnary rNonempty
            cases boundary with
            | inl sameMR =>
                cases data.right.right with
                | intro tail tailData =>
                    exact False.elim
                      (NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
                        (h := BHist.e1 rTail) (k := M) (tail := tail)
                        tailData.left tailData.right.left tailData.right.right
                        (hsame_symm sameMR))
            | inr MLtR =>
                exact False.elim (NatUnaryStrictPrefix_asymm MLtR data.right.right)
  · intro rEmpty
    cases divrem with
    | intro mq data =>
        cases rEmpty
        have sameMqN : hsame mq n :=
          hsame_symm (cont_right_unit_iff.mp data.right.left.right.right)
        exact
          (NatDivides_dividend_hsame_transport
            (Exists.intro q (And.intro (NatMul_right_unary data.left) data.left))
            sameMqN).right

theorem not_dvd_of_rem_pos {M n q r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> NatDivRem M n q r ->
      NatUnaryStrictPrefix BHist.Empty r -> NatDivides M n -> False := by
  intro MUnary MNonempty divrem rPositive divides
  have rEmpty := (dvd_iff_rem_zero MUnary MNonempty divrem).mp divides
  cases rEmpty
  exact NatUnaryStrictPrefix_empty_right_absurd rPositive

private theorem NatUnaryStrictPrefix_reverse_cont_absurd {r M tail : BHist} :
    NatUnaryStrictPrefix r M -> UnaryHistory tail -> Cont M tail r -> False := by
  intro strict tailUnary reverseCont
  cases tail with
  | Empty =>
      have sameRM : hsame r M := cont_right_unit_iff.mp reverseCont
      cases strict with
      | intro strictTail strictData =>
          exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
            strictData.left strictData.right.left strictData.right.right sameRM
  | e0 tail =>
      cases tailUnary
  | e1 tail =>
      have forward : NatUnaryStrictPrefix M r :=
        ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), reverseCont⟩
      exact NatUnaryStrictPrefix_asymm forward strict

private theorem NatDivRem_quotient_extension_absurd
    {M n q r q' r' tail : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      NatDivRem M n q r -> NatDivRem M n q' r' ->
        UnaryHistory tail -> (tail = BHist.Empty -> False) -> Cont q tail q' ->
          False := by
  intro MUnary MNonempty left right tailUnary tailNonempty qTail
  cases left with
  | intro mq leftData =>
      cases right with
      | intro mq' rightData =>
          have tailProduct := NatMul_total MUnary tailUnary
          cases tailProduct with
          | intro mt mtData =>
              have combined : NatMul M (append q tail) (append mq mt) :=
                NatMul_append_cont leftData.left mtData.right (cont_intro rfl)
              have combinedShifted : NatMul M q' (append mq mt) :=
                (NatMul_multiplier_hsame_transport combined (hsame_symm qTail)).right
              have sameMq' : hsame mq' (append mq mt) :=
                NatMul_functional MUnary rightData.left combinedShifted
              have rightDisplayed : Cont (append mq mt) r' n :=
                cont_hsame_transport sameMq' (hsame_refl r') (hsame_refl n)
                  rightData.right.left.right.right
              have nestedDisplayed : Cont mq (append mt r') n := by
                exact cont_intro
                  (rightDisplayed.trans (append_assoc mq mt r'))
              have sameR : hsame r (append mt r') :=
                cont_left_cancel leftData.right.left.right.right nestedDisplayed
              have quotientExtension :=
                NatMul_nonempty_quotient_product_extension MUnary tailUnary
                  mtData.right tailNonempty
              cases quotientExtension with
              | intro suffix suffixData =>
                  have reverseCont : Cont M (append suffix r') r := by
                    exact cont_intro
                      (sameR.trans
                        ((congrArg (fun h => append h r') suffixData.right).trans
                          (append_assoc M suffix r')))
                  exact NatUnaryStrictPrefix_reverse_cont_absurd leftData.right.right
                    (unary_append_closed suffixData.left (NatAdd_right_unary rightData.right.left))
                    reverseCont

theorem divRem_unique {M n q r q' r' : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      NatDivRem M n q r -> NatDivRem M n q' r' -> hsame q q' ∧ hsame r r' := by
  intro MUnary MNonempty left right
  have qUnary : UnaryHistory q := NatDivRem_quotient_unary left
  have q'Unary : UnaryHistory q' := NatDivRem_quotient_unary right
  have total := NatUnaryPrefix_total qUnary q'Unary
  have sameQ : hsame q q' := by
    cases total with
    | inl qPrefix =>
        cases qPrefix with
        | intro tail tailData =>
            cases tail with
            | Empty =>
                exact hsame_symm (cont_right_unit_iff.mp tailData.right)
            | e0 tail =>
                cases tailData.left
            | e1 tail =>
                exact False.elim
                  (NatDivRem_quotient_extension_absurd MUnary MNonempty left right
                    tailData.left (fun empty => by cases empty) tailData.right)
    | inr q'Prefix =>
        cases q'Prefix with
        | intro tail tailData =>
            cases tail with
            | Empty =>
                exact cont_right_unit_iff.mp tailData.right
            | e0 tail =>
                cases tailData.left
            | e1 tail =>
                exact False.elim
                  (NatDivRem_quotient_extension_absurd MUnary MNonempty right left
                    tailData.left (fun empty => by cases empty) tailData.right)
  constructor
  · exact sameQ
  · cases left with
    | intro mq leftData =>
        cases right with
        | intro mq' rightData =>
            have rightAtQ : NatMul M q mq' :=
              (NatMul_multiplier_hsame_transport rightData.left (hsame_symm sameQ)).right
            have sameProducts : hsame mq mq' :=
              NatMul_functional MUnary leftData.left rightAtQ
            have rightDisplayedAtLeftProduct : Cont mq r' n :=
              cont_hsame_transport (hsame_symm sameProducts) (hsame_refl r')
                (hsame_refl n) rightData.right.left.right.right
            exact cont_left_cancel leftData.right.left.right.right rightDisplayedAtLeftProduct

end BEDC.Derived.PrimeUp
