import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.Derived.NatUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

inductive NatMul (d : BHist) : BHist -> BHist -> Prop where
  | zero (hd : UnaryHistory d) : NatMul d BHist.Empty BHist.Empty
  | succ {q n n' : BHist} : NatMul d q n -> Cont n d n' -> NatMul d (BHist.e1 q) n'

theorem NatMul_total {d q : BHist} :
    UnaryHistory d -> UnaryHistory q -> exists n : BHist, UnaryHistory n /\ NatMul d q n := by
  intro hd hq
  induction q with
  | Empty =>
      exact ⟨BHist.Empty, unary_empty, NatMul.zero hd⟩
  | e0 q ih =>
      cases hq
  | e1 q ih =>
      have previous := ih hq
      cases previous with
      | intro n data =>
          exact ⟨append n d, unary_cont_closed data.left hd (cont_intro rfl),
            NatMul.succ data.right (cont_intro rfl)⟩

theorem NatMul_functional {d q n m : BHist} :
    UnaryHistory d -> NatMul d q n -> NatMul d q m -> hsame n m := by
  intro _hd left
  induction left generalizing m with
  | zero _hdZero =>
      intro right
      cases right with
      | zero _hdRight =>
          rfl
  | succ leftPrev leftCont ih =>
      intro right
      cases right with
      | succ rightPrev rightCont =>
          have samePrev : hsame _ _ := ih rightPrev
          exact cont_respects_hsame samePrev (hsame_refl d) leftCont rightCont

theorem NatMul_left_unary {d q n : BHist} : NatMul d q n -> UnaryHistory d := by
  intro mul
  induction mul with
  | zero hd => exact hd
  | succ _ _ ih => exact ih

theorem NatMul_right_unary {d q n : BHist} : NatMul d q n -> UnaryHistory q := by
  intro mul
  induction mul with
  | zero _hd =>
      exact unary_empty
  | succ _prev _step ih =>
      exact unary_e1_closed ih

theorem NatMul_result_unary {d q n : BHist} :
    UnaryHistory d -> NatMul d q n -> UnaryHistory n := by
  intro hd mul
  induction mul with
  | zero _hd =>
      exact unary_empty
  | succ _prev step ih =>
      exact unary_cont_closed ih hd step

theorem NatMul_append_cont {d q e w n r : BHist} :
    NatMul d w n -> NatMul d q e -> Cont n e r -> NatMul d (append w q) r := by
  intro left right continuation
  induction right generalizing w n r with
  | zero _hd =>
      cases continuation
      exact left
  | succ prev step ih =>
      cases step
      cases continuation
      exact NatMul.succ (ih left (cont_intro rfl)) (cont_intro (append_assoc n _ d).symm)

theorem NatMul_succ_inversion {d q n' : BHist} :
    NatMul d (BHist.e1 q) n' -> exists n : BHist, NatMul d q n ∧ Cont n d n' := by
  intro mul
  cases mul with
  | succ prev step =>
      exact ⟨_, prev, step⟩

theorem NatMul_empty_left_result_empty {q n : BHist} :
    NatMul BHist.Empty q n -> hsame n BHist.Empty := by
  intro mul
  induction mul with
  | zero _ =>
      rfl
  | succ _ step ih =>
      have emptyResult : hsame _ BHist.Empty := ih
      cases emptyResult
      exact cont_left_unit_result step

theorem NatMul_unit_left_hsame {q n : BHist} :
    UnaryHistory q -> NatMul (BHist.e1 BHist.Empty) q n -> hsame n q := by
  intro hq hmul
  induction hmul with
  | zero _hd =>
      rfl
  | succ _prev step ih =>
      have tailUnary : UnaryHistory _ := unary_e1_inversion hq
      have prevSame := ih tailUnary
      cases prevSame
      exact cont_deterministic step (cont_intro rfl)

theorem NatMul_unit_right_hsame {d n : BHist} :
    NatMul d (BHist.e1 BHist.Empty) n -> hsame n d := by
  intro hmul
  cases hmul with
  | succ previous step =>
      cases previous with
      | zero _hd =>
          exact step.trans (append_empty_left d)

theorem NatMul_e0_multiplier_absurd {d q n : BHist} :
    NatMul d (BHist.e0 q) n -> False := by
  intro mul
  cases mul

theorem NatMul_nonempty_multiplicand_empty_result_iff {d q : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) ->
      (NatMul d q BHist.Empty <-> hsame q BHist.Empty) := by
  intro hd dNonempty
  constructor
  · intro mul
    cases mul with
    | zero _hd =>
        rfl
    | succ _prev step =>
        have emptyParts := cont_empty_result_inversion step
        exact False.elim (dNonempty emptyParts.right)
  · intro qEmpty
    cases qEmpty
    exact NatMul.zero hd

theorem NatMul_append_cont_empty_result_empty_factors_iff {d w q n e r : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) ->
      NatMul d w n -> NatMul d q e -> Cont n e r ->
        (hsame r BHist.Empty <-> hsame w BHist.Empty ∧ hsame q BHist.Empty) := by
  intro hd dNonempty left right continuation
  have combined : NatMul d (append w q) r := NatMul_append_cont left right continuation
  have resultIff : NatMul d (append w q) BHist.Empty <-> hsame (append w q) BHist.Empty :=
    NatMul_nonempty_multiplicand_empty_result_iff hd dNonempty
  constructor
  · intro resultEmpty
    cases resultEmpty
    exact append_eq_empty_iff.mp (Iff.mp resultIff combined)
  · intro partsEmpty
    have emptyProduct : NatMul d (append w q) BHist.Empty :=
      Iff.mpr resultIff (append_eq_empty_iff.mpr partsEmpty)
    exact NatMul_functional hd combined emptyProduct

theorem NatMul_succ_result_empty_left_empty {d q n : BHist} :
    NatMul d (BHist.e1 q) n -> hsame n BHist.Empty -> hsame d BHist.Empty := by
  intro mul resultEmpty
  cases resultEmpty
  cases mul with
  | succ _prev step =>
      exact (cont_empty_result_inversion step).right

def NatDivides (d n : BHist) : Prop :=
  ∃ q : BHist, UnaryHistory q ∧ NatMul d q n

theorem NatDivides_empty_left_result_empty {n : BHist} :
    NatDivides BHist.Empty n -> hsame n BHist.Empty := by
  intro divides
  cases divides with
  | intro _ qData =>
      exact NatMul_empty_left_result_empty qData.right

theorem NatDivides_reflexive_pair {n : BHist} :
    UnaryHistory n ->
      NatDivides (BHist.e1 BHist.Empty) n ∧ NatDivides n n := by
  intro hn
  constructor
  · induction n with
    | Empty =>
        exact ⟨BHist.Empty, unary_empty, NatMul.zero (unary_e1_closed unary_empty)⟩
    | e0 n ih =>
        cases hn
    | e1 n ih =>
        have unitDividesTail := ih hn
        cases unitDividesTail with
        | intro q qData =>
            cases qData with
            | intro qUnary qMul =>
                exact ⟨BHist.e1 q, unary_e1_closed qUnary,
                  NatMul.succ qMul (cont_intro rfl)⟩
  · exact ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty,
      NatMul.succ (NatMul.zero hn) (cont_left_unit n)⟩

theorem NatDivides_transitive {d e n : BHist} :
    NatDivides d e -> NatDivides e n -> NatDivides d n := by
  intro left right
  cases left with
  | intro q qData =>
      cases qData with
      | intro qUnary qMul =>
          cases right with
          | intro r rData =>
              cases rData with
              | intro rUnary rMul =>
                  induction rMul with
                  | zero _eUnary =>
                      exact ⟨BHist.Empty, unary_empty, NatMul.zero (NatMul_left_unary qMul)⟩
                  | succ prev step ih =>
                      cases ih rUnary with
                      | intro w wData =>
                          cases wData with
                          | intro wUnary wMul =>
                              exact ⟨append w q, unary_append_closed wUnary qUnary,
                                NatMul_append_cont wMul qMul step⟩

theorem NatDivides_reflexive {n : BHist} :
    UnaryHistory n -> NatDivides (BHist.e1 BHist.Empty) n ∧ NatDivides n n := by
  intro hn
  constructor
  · have unitMul : NatMul (BHist.e1 BHist.Empty) n n := by
      induction n with
      | Empty =>
          exact NatMul.zero (unary_e1_closed unary_empty)
      | e0 n ih =>
          cases hn
      | e1 n ih =>
          have hnTail : UnaryHistory n := unary_e1_inversion hn
          exact NatMul.succ (ih hnTail) (cont_intro rfl)
    exact ⟨n, hn, unitMul⟩
  · exact ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty,
      NatMul.succ (NatMul.zero hn) (cont_left_unit n)⟩

theorem NatDivides_unit_self_reflexive {n : BHist} :
    UnaryHistory n -> NatDivides (BHist.e1 BHist.Empty) n ∧ NatDivides n n := by
  intro hn
  constructor
  · have total :=
      NatMul_total (d := BHist.e1 BHist.Empty) (q := n)
        (unary_e1_closed unary_empty) hn
    cases total with
    | intro m data =>
        have sameMN : hsame m n := NatMul_unit_left_hsame hn data.right
        cases sameMN
        exact Exists.intro n (And.intro hn data.right)
  · exact
      Exists.intro (BHist.e1 BHist.Empty)
        (And.intro (unary_e1_closed unary_empty)
          (NatMul.succ (NatMul.zero hn) (cont_intro (append_empty_left n).symm)))

def NatPrime (p : BHist) : Prop :=
  UnaryHistory p ∧ NatUnaryStrictPrefix (BHist.e1 BHist.Empty) p ∧
    ∀ d : BHist, UnaryHistory d -> NatDivides d p ->
      hsame d (BHist.e1 BHist.Empty) ∨ hsame d p

theorem NatPrime_first_pair :
    NatPrime (BHist.e1 (BHist.e1 BHist.Empty)) ∧
      NatPrime (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty))) := by
  have emptyFactor_result_empty :
      ∀ {q n : BHist}, NatMul BHist.Empty q n -> hsame n BHist.Empty := by
    intro _ _ mul
    exact NatMul_empty_left_result_empty mul
  have largeDivisor_not_two :
      ∀ {d q : BHist}, NatMul (BHist.e1 (BHist.e1 (BHist.e1 d))) q
        (BHist.e1 (BHist.e1 BHist.Empty)) -> False := by
    intro d q mul
    cases mul with
    | succ _ step =>
        cases step
  have two_not_divides_three :
      ∀ {q : BHist}, NatMul (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e1 q)
        (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty))) -> False := by
    intro q mul
    cases mul with
    | succ prev step =>
        cases prev with
        | zero _ =>
            cases step
        | succ _ prevStep =>
            cases prevStep
            cases step
  have largeDivisor_not_three :
      ∀ {d q : BHist}, NatMul (BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 d)))) q
        (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty))) -> False := by
    intro d q mul
    cases mul with
    | succ _ step =>
        cases step
  constructor
  · constructor
    · exact unary_e1_closed (unary_e1_closed unary_empty)
    · constructor
      · exact ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty,
          (fun empty => by cases empty), cont_intro rfl⟩
      · intro d hd divides
        cases d with
        | Empty =>
            cases divides with
            | intro q qData =>
                have zeroResult :
                    hsame (BHist.e1 (BHist.e1 BHist.Empty)) BHist.Empty :=
                  emptyFactor_result_empty qData.right
                exact False.elim (not_hsame_e1_empty zeroResult)
        | e0 d =>
            cases hd
        | e1 d =>
            cases d with
            | Empty =>
                exact Or.inl rfl
            | e0 d =>
                cases hd
            | e1 d =>
                cases d with
                | Empty =>
                    exact Or.inr rfl
                | e0 d =>
                    cases hd
                | e1 d =>
                    cases divides with
                    | intro q qData =>
                        exact False.elim (largeDivisor_not_two qData.right)
  · constructor
    · exact unary_e1_closed (unary_e1_closed (unary_e1_closed unary_empty))
    · constructor
      · exact ⟨BHist.e1 (BHist.e1 BHist.Empty),
          unary_e1_closed (unary_e1_closed unary_empty),
          (fun empty => by cases empty), cont_intro rfl⟩
      · intro d hd divides
        cases d with
        | Empty =>
            cases divides with
            | intro q qData =>
                have zeroResult :
                    hsame (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty))) BHist.Empty :=
                  emptyFactor_result_empty qData.right
                exact False.elim (not_hsame_e1_empty zeroResult)
        | e0 d =>
            cases hd
        | e1 d =>
            cases d with
            | Empty =>
                exact Or.inl rfl
            | e0 d =>
                cases hd
            | e1 d =>
                cases d with
                | Empty =>
                    cases divides with
                    | intro q qData =>
                        cases q with
                        | Empty =>
                            cases qData.right
                        | e0 q =>
                            cases qData.left
                        | e1 q =>
                            exact False.elim (two_not_divides_three qData.right)
                | e0 d =>
                    cases hd
                | e1 d =>
                    cases d with
                    | Empty =>
                        exact Or.inr rfl
                    | e0 d =>
                        cases hd
                    | e1 d =>
                        cases divides with
                        | intro q qData =>
                            exact False.elim (largeDivisor_not_three qData.right)

theorem NatPrime_NatMul_succ_result_not_empty {p q n : BHist} :
    NatPrime p -> NatMul p (BHist.e1 q) n -> hsame n BHist.Empty -> False := by
  intro prime mul resultEmpty
  have multiplicandEmpty := NatMul_succ_result_empty_left_empty mul resultEmpty
  cases multiplicandEmpty
  exact NatUnaryStrictPrefix_empty_right_absurd prime.right.left

theorem NatMul_first_prime_unit_result :
    NatMul (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty)
      (BHist.e1 (BHist.e1 BHist.Empty)) := by
  have primeTwo : NatPrime (BHist.e1 (BHist.e1 BHist.Empty)) := NatPrime_first_pair.left
  exact NatMul.succ (NatMul.zero primeTwo.left)
    (cont_left_unit (BHist.e1 (BHist.e1 BHist.Empty)))

inductive NatFact : BHist -> BHist -> Prop where
  | zero : NatFact BHist.Empty (BHist.e1 BHist.Empty)
  | succ {n m m' : BHist} : NatFact n m -> NatMul (BHist.e1 n) m m' ->
      NatFact (BHist.e1 n) m'

theorem NatFact_result_not_empty {n m : BHist} :
    NatFact n m -> hsame m BHist.Empty -> False := by
  intro fact
  induction fact with
  | zero =>
      intro resultEmpty
      exact not_hsame_e1_empty resultEmpty
  | succ _prevFact mul ih =>
      intro resultEmpty
      cases resultEmpty
      have previousEmpty : hsame _ BHist.Empty :=
        Iff.mp
          (NatMul_nonempty_multiplicand_empty_result_iff
            (NatMul_left_unary mul) not_hsame_e1_empty)
          mul
      exact ih previousEmpty

theorem NatFact_result_unary {n m : BHist} : NatFact n m -> UnaryHistory m := by
  intro fact
  induction fact with
  | zero =>
      exact unary_e1_closed unary_empty
  | succ _previous mul _ih =>
      exact NatMul_result_unary (NatMul_left_unary mul) mul

theorem NatFact_total_functional {n : BHist} :
    UnaryHistory n ->
      (exists m : BHist, UnaryHistory m /\ NatFact n m) /\
        (forall {m m' : BHist}, NatFact n m -> NatFact n m' -> hsame m m') := by
  intro hn
  induction n with
  | Empty =>
      constructor
      · exact ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, NatFact.zero⟩
      · intro m m' left right
        cases left
        cases right
        rfl
  | e0 n ih =>
      cases hn
  | e1 n ih =>
      have hnTail : UnaryHistory n := unary_e1_inversion hn
      have ihData := ih hnTail
      cases ihData with
      | intro ihTotal ihFunctional =>
          constructor
          · cases ihTotal with
            | intro m data =>
                have next :=
                  NatMul_total (d := BHist.e1 n) (q := m)
                    (unary_e1_closed hnTail) data.left
                cases next with
                | intro m' nextData =>
                    exact ⟨m', nextData.left, NatFact.succ data.right nextData.right⟩
          · intro m m' left right
            cases left with
            | succ leftFact leftMul =>
                cases right with
                | succ rightFact rightMul =>
                    have sameFactor : hsame _ _ := ihFunctional leftFact rightFact
                    cases sameFactor
                    exact NatMul_functional (unary_e1_closed hnTail) leftMul rightMul

inductive TrialDiv : BHist -> BHist -> Prop where
  | unit {n : BHist} (hn : UnaryHistory n) : TrialDiv (BHist.e1 BHist.Empty) n
  | step {b n b' : BHist} :
      TrialDiv b n ->
        ((NatDivides b n -> False) \/ hsame b (BHist.e1 BHist.Empty) \/ hsame b n) ->
          Cont b (BHist.e1 BHist.Empty) b' ->
            TrialDiv b' n

theorem TrialDiv_step_unary_closed {b n b' : BHist} :
    TrialDiv b n ->
      ((NatDivides b n -> False) \/ hsame b (BHist.e1 BHist.Empty) \/ hsame b n) ->
        Cont b (BHist.e1 BHist.Empty) b' -> UnaryHistory b' /\ TrialDiv b' n := by
  intro trial
  induction trial generalizing b' with
  | unit hn =>
      intro advance stepCont
      exact ⟨unary_cont_closed (unary_e1_closed unary_empty)
          (unary_e1_closed unary_empty) stepCont,
        TrialDiv.step (TrialDiv.unit hn) advance stepCont⟩
  | step prevTrial prevAdvance prevStep ih =>
      intro advance stepCont
      have prevClosed := ih prevAdvance prevStep
      exact ⟨unary_cont_closed prevClosed.left (unary_e1_closed unary_empty) stepCont,
        TrialDiv.step (TrialDiv.step prevTrial prevAdvance prevStep) advance stepCont⟩

theorem TrialDiv_bound_unary {b n : BHist} : TrialDiv b n -> UnaryHistory b := by
  intro trial
  induction trial with
  | unit _hn =>
      exact unary_e1_closed unary_empty
  | step _trial _screen stepCont ih =>
      exact unary_cont_closed ih (unary_e1_closed unary_empty) stepCont

end BEDC.Derived.PrimeUp
