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

def NatDivides (d n : BHist) : Prop :=
  ∃ q : BHist, UnaryHistory q ∧ NatMul d q n

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
