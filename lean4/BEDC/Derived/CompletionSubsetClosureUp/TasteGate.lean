import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionSubsetClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionSubsetClosureUp : Type where
  | mk (M E D P S W Q R L H C G N : BHist) : CompletionSubsetClosureUp
  deriving DecidableEq

def completionSubsetClosureEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionSubsetClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionSubsetClosureEncodeBHist h

def completionSubsetClosureDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionSubsetClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionSubsetClosureDecodeBHist tail)

private theorem CompletionSubsetClosure_decode_encode :
    forall h : BHist,
      completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionSubsetClosureFields : CompletionSubsetClosureUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionSubsetClosureUp.mk M E D P S W Q R L H C G N =>
      [M, E, D, P, S, W, Q, R, L, H, C, G, N]

def completionSubsetClosureToEventFlow : CompletionSubsetClosureUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completionSubsetClosureFields x).map completionSubsetClosureEncodeBHist

private def completionSubsetClosureEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionSubsetClosureEventAtDefault index rest

def completionSubsetClosureFromEventFlow : EventFlow -> Option CompletionSubsetClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompletionSubsetClosureUp.mk
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 0 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 1 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 2 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 3 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 4 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 5 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 6 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 7 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 8 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 9 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 10 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 11 ef))
        (completionSubsetClosureDecodeBHist (completionSubsetClosureEventAtDefault 12 ef)))

private theorem CompletionSubsetClosure_round_trip :
    forall x : CompletionSubsetClosureUp,
      completionSubsetClosureFromEventFlow (completionSubsetClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E D P S W Q R L H C G N =>
      change
        some
            (CompletionSubsetClosureUp.mk
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist M))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist E))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist D))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist P))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist S))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist W))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist Q))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist R))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist L))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist H))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist C))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist G))
              (completionSubsetClosureDecodeBHist (completionSubsetClosureEncodeBHist N))) =
          some (CompletionSubsetClosureUp.mk M E D P S W Q R L H C G N)
      rw [CompletionSubsetClosure_decode_encode M, CompletionSubsetClosure_decode_encode E,
        CompletionSubsetClosure_decode_encode D, CompletionSubsetClosure_decode_encode P,
        CompletionSubsetClosure_decode_encode S, CompletionSubsetClosure_decode_encode W,
        CompletionSubsetClosure_decode_encode Q, CompletionSubsetClosure_decode_encode R,
        CompletionSubsetClosure_decode_encode L, CompletionSubsetClosure_decode_encode H,
        CompletionSubsetClosure_decode_encode C, CompletionSubsetClosure_decode_encode G,
        CompletionSubsetClosure_decode_encode N]

private theorem CompletionSubsetClosure_toEventFlow_injective
    {x y : CompletionSubsetClosureUp} :
    completionSubsetClosureToEventFlow x = completionSubsetClosureToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionSubsetClosureFromEventFlow (completionSubsetClosureToEventFlow x) =
        completionSubsetClosureFromEventFlow (completionSubsetClosureToEventFlow y) :=
    congrArg completionSubsetClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionSubsetClosure_round_trip x).symm
      (Eq.trans hread (CompletionSubsetClosure_round_trip y)))

private theorem CompletionSubsetClosure_fields_faithful :
    forall x y : CompletionSubsetClosureUp,
      completionSubsetClosureFields x = completionSubsetClosureFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 E1 D1 P1 S1 W1 Q1 R1 L1 H1 C1 G1 N1 =>
      cases y with
      | mk M2 E2 D2 P2 S2 W2 Q2 R2 L2 H2 C2 G2 N2 =>
          injection hfields with hM tail0
          injection tail0 with hE tail1
          injection tail1 with hD tail2
          injection tail2 with hP tail3
          injection tail3 with hS tail4
          injection tail4 with hW tail5
          injection tail5 with hQ tail6
          injection tail6 with hR tail7
          injection tail7 with hL tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hG tail11
          injection tail11 with hN _
          subst hM
          subst hE
          subst hD
          subst hP
          subst hS
          subst hW
          subst hQ
          subst hR
          subst hL
          subst hH
          subst hC
          subst hG
          subst hN
          rfl

instance completionSubsetClosureBHistCarrier : BHistCarrier CompletionSubsetClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionSubsetClosureToEventFlow
  fromEventFlow := completionSubsetClosureFromEventFlow

instance completionSubsetClosureChapterTasteGate :
    ChapterTasteGate CompletionSubsetClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionSubsetClosureFromEventFlow (completionSubsetClosureToEventFlow x) = some x
    exact CompletionSubsetClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionSubsetClosure_toEventFlow_injective heq)

instance completionSubsetClosureFieldFaithful : FieldFaithful CompletionSubsetClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionSubsetClosureFields
  field_faithful := CompletionSubsetClosure_fields_faithful

instance completionSubsetClosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompletionSubsetClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionSubsetClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompletionSubsetClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompletionSubsetClosure_namecert_obligations :
    Nonempty (ChapterTasteGate CompletionSubsetClosureUp) ∧
      Nonempty (FieldFaithful CompletionSubsetClosureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompletionSubsetClosureUp) ∧
          (∀ M E D P S W Q R L H C G N : BHist,
            completionSubsetClosureFields
                (CompletionSubsetClosureUp.mk M E D P S W Q R L H C G N) =
              [M, E, D, P, S, W, Q, R, L, H, C, G, N]) ∧
            (∀ h : BHist,
              completionSubsetClosureDecodeBHist
                  (completionSubsetClosureEncodeBHist h) =
                h) ∧
              completionSubsetClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨completionSubsetClosureChapterTasteGate⟩,
      ⟨completionSubsetClosureFieldFaithful⟩,
      ⟨completionSubsetClosureNontrivial⟩,
      (by
        intro M E D P S W Q R L H C G N
        rfl),
      CompletionSubsetClosure_decode_encode,
      rfl⟩

end BEDC.Derived.CompletionSubsetClosureUp
