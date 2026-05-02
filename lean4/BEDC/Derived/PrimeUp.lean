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

def NatDivides (d n : BHist) : Prop :=
  ∃ q : BHist, UnaryHistory q ∧ NatMul d q n

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

inductive NatFact : BHist -> BHist -> Prop where
  | zero : NatFact BHist.Empty (BHist.e1 BHist.Empty)
  | succ {n m m' : BHist} : NatFact n m -> NatMul (BHist.e1 n) m m' ->
      NatFact (BHist.e1 n) m'

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

end BEDC.Derived.PrimeUp
