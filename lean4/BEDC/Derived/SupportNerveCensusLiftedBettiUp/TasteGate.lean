import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SupportNerveCensusLiftedBettiUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SupportNerveCensusLiftedBettiUp : Type where
  | mk (I U V F H0 B L G C P N : BHist) : SupportNerveCensusLiftedBettiUp
  deriving DecidableEq

def supportNerveCensusLiftedBettiEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: supportNerveCensusLiftedBettiEncodeBHist h
  | BHist.e1 h => BMark.b1 :: supportNerveCensusLiftedBettiEncodeBHist h

def supportNerveCensusLiftedBettiDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (supportNerveCensusLiftedBettiDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (supportNerveCensusLiftedBettiDecodeBHist tail)

private theorem supportNerveCensusLiftedBetti_decode_encode_bhist :
    forall h : BHist,
      supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def supportNerveCensusLiftedBettiFields :
    SupportNerveCensusLiftedBettiUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SupportNerveCensusLiftedBettiUp.mk I U V F H0 B L G C P N =>
      [I, U, V, F, H0, B, L, G, C, P, N]

def supportNerveCensusLiftedBettiToEventFlow :
    SupportNerveCensusLiftedBettiUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (supportNerveCensusLiftedBettiFields x).map
      supportNerveCensusLiftedBettiEncodeBHist

private def supportNerveCensusLiftedBettiEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => supportNerveCensusLiftedBettiEventAtDefault index rest

def supportNerveCensusLiftedBettiFromEventFlow
    (ef : EventFlow) : Option SupportNerveCensusLiftedBettiUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SupportNerveCensusLiftedBettiUp.mk
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 0 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 1 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 2 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 3 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 4 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 5 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 6 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 7 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 8 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 9 ef))
      (supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEventAtDefault 10 ef)))

private theorem supportNerveCensusLiftedBetti_round_trip :
    forall x : SupportNerveCensusLiftedBettiUp,
      supportNerveCensusLiftedBettiFromEventFlow
        (supportNerveCensusLiftedBettiToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I U V F H0 B L G C P N =>
      change
        some
            (SupportNerveCensusLiftedBettiUp.mk
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist I))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist U))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist V))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist F))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist H0))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist B))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist L))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist G))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist C))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist P))
              (supportNerveCensusLiftedBettiDecodeBHist
                (supportNerveCensusLiftedBettiEncodeBHist N))) =
          some (SupportNerveCensusLiftedBettiUp.mk I U V F H0 B L G C P N)
      rw [supportNerveCensusLiftedBetti_decode_encode_bhist I,
        supportNerveCensusLiftedBetti_decode_encode_bhist U,
        supportNerveCensusLiftedBetti_decode_encode_bhist V,
        supportNerveCensusLiftedBetti_decode_encode_bhist F,
        supportNerveCensusLiftedBetti_decode_encode_bhist H0,
        supportNerveCensusLiftedBetti_decode_encode_bhist B,
        supportNerveCensusLiftedBetti_decode_encode_bhist L,
        supportNerveCensusLiftedBetti_decode_encode_bhist G,
        supportNerveCensusLiftedBetti_decode_encode_bhist C,
        supportNerveCensusLiftedBetti_decode_encode_bhist P,
        supportNerveCensusLiftedBetti_decode_encode_bhist N]

private theorem supportNerveCensusLiftedBettiToEventFlow_injective
    {x y : SupportNerveCensusLiftedBettiUp} :
    supportNerveCensusLiftedBettiToEventFlow x =
      supportNerveCensusLiftedBettiToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      supportNerveCensusLiftedBettiFromEventFlow
          (supportNerveCensusLiftedBettiToEventFlow x) =
        supportNerveCensusLiftedBettiFromEventFlow
          (supportNerveCensusLiftedBettiToEventFlow y) :=
    congrArg supportNerveCensusLiftedBettiFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (supportNerveCensusLiftedBetti_round_trip x).symm
      (Eq.trans hread (supportNerveCensusLiftedBetti_round_trip y)))

private theorem supportNerveCensusLiftedBetti_fields_faithful :
    forall x y : SupportNerveCensusLiftedBettiUp,
      supportNerveCensusLiftedBettiFields x =
        supportNerveCensusLiftedBettiFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 U1 V1 F1 H01 B1 L1 G1 C1 P1 N1 =>
      cases y with
      | mk I2 U2 V2 F2 H02 B2 L2 G2 C2 P2 N2 =>
          cases hfields
          rfl

instance supportNerveCensusLiftedBettiBHistCarrier :
    BHistCarrier SupportNerveCensusLiftedBettiUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := supportNerveCensusLiftedBettiToEventFlow
  fromEventFlow := supportNerveCensusLiftedBettiFromEventFlow

instance supportNerveCensusLiftedBettiChapterTasteGate :
    ChapterTasteGate SupportNerveCensusLiftedBettiUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      supportNerveCensusLiftedBettiFromEventFlow
          (supportNerveCensusLiftedBettiToEventFlow x) = some x
    exact supportNerveCensusLiftedBetti_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (supportNerveCensusLiftedBettiToEventFlow_injective heq)

instance supportNerveCensusLiftedBettiFieldFaithful :
    FieldFaithful SupportNerveCensusLiftedBettiUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := supportNerveCensusLiftedBettiFields
  field_faithful := supportNerveCensusLiftedBetti_fields_faithful

instance supportNerveCensusLiftedBettiNontrivial :
    Nontrivial SupportNerveCensusLiftedBettiUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SupportNerveCensusLiftedBettiUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SupportNerveCensusLiftedBettiUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SupportNerveCensusLiftedBettiUp :=
  -- BEDC touchpoint anchor: BHist BMark
  supportNerveCensusLiftedBettiChapterTasteGate

theorem SupportNerveCensusLiftedBettiTasteGate_single_carrier_alignment :
    (forall h : BHist,
      supportNerveCensusLiftedBettiDecodeBHist
        (supportNerveCensusLiftedBettiEncodeBHist h) = h) ∧
      (forall x : SupportNerveCensusLiftedBettiUp,
        supportNerveCensusLiftedBettiFromEventFlow
          (supportNerveCensusLiftedBettiToEventFlow x) = some x) ∧
        (forall x y : SupportNerveCensusLiftedBettiUp,
          supportNerveCensusLiftedBettiToEventFlow x =
            supportNerveCensusLiftedBettiToEventFlow y -> x = y) ∧
          supportNerveCensusLiftedBettiEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨supportNerveCensusLiftedBetti_decode_encode_bhist,
      supportNerveCensusLiftedBetti_round_trip,
      (fun _ _ heq => supportNerveCensusLiftedBettiToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SupportNerveCensusLiftedBettiUp
