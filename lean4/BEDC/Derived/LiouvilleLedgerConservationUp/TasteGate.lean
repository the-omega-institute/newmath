import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LiouvilleLedgerConservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LiouvilleLedgerConservationUp : Type where
  | mk (S T K G Q H C P N : BHist) : LiouvilleLedgerConservationUp
  deriving DecidableEq

def liouvilleLedgerConservationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: liouvilleLedgerConservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: liouvilleLedgerConservationEncodeBHist h

def liouvilleLedgerConservationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (liouvilleLedgerConservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (liouvilleLedgerConservationDecodeBHist tail)

private theorem LiouvilleLedgerConservation_decode_encode :
    forall h : BHist,
      liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def liouvilleLedgerConservationFields : LiouvilleLedgerConservationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LiouvilleLedgerConservationUp.mk S T K G Q H C P N => [S, T, K, G, Q, H, C, P, N]

def liouvilleLedgerConservationToEventFlow :
    LiouvilleLedgerConservationUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (liouvilleLedgerConservationFields x).map liouvilleLedgerConservationEncodeBHist

private def liouvilleLedgerConservationEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => liouvilleLedgerConservationEventAtDefault index rest

def liouvilleLedgerConservationFromEventFlow :
    EventFlow -> Option LiouvilleLedgerConservationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LiouvilleLedgerConservationUp.mk
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 0 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 1 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 2 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 3 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 4 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 5 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 6 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 7 ef))
        (liouvilleLedgerConservationDecodeBHist
          (liouvilleLedgerConservationEventAtDefault 8 ef)))

private theorem LiouvilleLedgerConservation_round_trip :
    forall x : LiouvilleLedgerConservationUp,
      liouvilleLedgerConservationFromEventFlow
          (liouvilleLedgerConservationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T K G Q H C P N =>
      change
        some
            (LiouvilleLedgerConservationUp.mk
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist S))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist T))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist K))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist G))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist Q))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist H))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist C))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist P))
              (liouvilleLedgerConservationDecodeBHist
                (liouvilleLedgerConservationEncodeBHist N))) =
          some (LiouvilleLedgerConservationUp.mk S T K G Q H C P N)
      rw [LiouvilleLedgerConservation_decode_encode S,
        LiouvilleLedgerConservation_decode_encode T,
        LiouvilleLedgerConservation_decode_encode K,
        LiouvilleLedgerConservation_decode_encode G,
        LiouvilleLedgerConservation_decode_encode Q,
        LiouvilleLedgerConservation_decode_encode H,
        LiouvilleLedgerConservation_decode_encode C,
        LiouvilleLedgerConservation_decode_encode P,
        LiouvilleLedgerConservation_decode_encode N]

private theorem LiouvilleLedgerConservation_toEventFlow_injective
    {x y : LiouvilleLedgerConservationUp} :
    liouvilleLedgerConservationToEventFlow x =
        liouvilleLedgerConservationToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      liouvilleLedgerConservationFromEventFlow (liouvilleLedgerConservationToEventFlow x) =
        liouvilleLedgerConservationFromEventFlow (liouvilleLedgerConservationToEventFlow y) :=
    congrArg liouvilleLedgerConservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LiouvilleLedgerConservation_round_trip x).symm
      (Eq.trans hread (LiouvilleLedgerConservation_round_trip y)))

private theorem LiouvilleLedgerConservation_fields_faithful :
    forall x y : LiouvilleLedgerConservationUp,
      liouvilleLedgerConservationFields x = liouvilleLedgerConservationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 K1 G1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 K2 G2 Q2 H2 C2 P2 N2 =>
          injection hfields with hS tail0
          injection tail0 with hT tail1
          injection tail1 with hK tail2
          injection tail2 with hG tail3
          injection tail3 with hQ tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hS
          subst hT
          subst hK
          subst hG
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance liouvilleLedgerConservationBHistCarrier :
    BHistCarrier LiouvilleLedgerConservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := liouvilleLedgerConservationToEventFlow
  fromEventFlow := liouvilleLedgerConservationFromEventFlow

instance liouvilleLedgerConservationChapterTasteGate :
    ChapterTasteGate LiouvilleLedgerConservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      liouvilleLedgerConservationFromEventFlow
          (liouvilleLedgerConservationToEventFlow x) =
        some x
    exact LiouvilleLedgerConservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LiouvilleLedgerConservation_toEventFlow_injective heq)

instance liouvilleLedgerConservationFieldFaithful :
    FieldFaithful LiouvilleLedgerConservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := liouvilleLedgerConservationFields
  field_faithful := LiouvilleLedgerConservation_fields_faithful

instance liouvilleLedgerConservationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LiouvilleLedgerConservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LiouvilleLedgerConservationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LiouvilleLedgerConservationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LiouvilleLedgerConservation_namecert_obligations :
    Nonempty (ChapterTasteGate LiouvilleLedgerConservationUp) ∧
      Nonempty (FieldFaithful LiouvilleLedgerConservationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LiouvilleLedgerConservationUp) ∧
          (∀ S T K G Q H C P N : BHist,
            liouvilleLedgerConservationFields
                (LiouvilleLedgerConservationUp.mk S T K G Q H C P N) =
              [S, T, K, G, Q, H, C, P, N]) ∧
            (∀ h : BHist,
              liouvilleLedgerConservationDecodeBHist
                  (liouvilleLedgerConservationEncodeBHist h) =
                h) ∧
              liouvilleLedgerConservationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨liouvilleLedgerConservationChapterTasteGate⟩,
      ⟨liouvilleLedgerConservationFieldFaithful⟩,
      ⟨liouvilleLedgerConservationNontrivial⟩,
      (by
        intro S T K G Q H C P N
        rfl),
      LiouvilleLedgerConservation_decode_encode,
      rfl⟩

end BEDC.Derived.LiouvilleLedgerConservationUp
