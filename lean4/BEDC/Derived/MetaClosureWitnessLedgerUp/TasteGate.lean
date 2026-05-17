import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaClosureWitnessLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaClosureWitnessLedgerUp : Type where
  | mk (W K D A R H C P N : BHist) : MetaClosureWitnessLedgerUp
  deriving DecidableEq

def metaClosureWitnessLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaClosureWitnessLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaClosureWitnessLedgerEncodeBHist h

def metaClosureWitnessLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaClosureWitnessLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaClosureWitnessLedgerDecodeBHist tail)

private theorem metaClosureWitnessLedgerDecode_encode_bhist :
    ∀ h : BHist,
      metaClosureWitnessLedgerDecodeBHist
        (metaClosureWitnessLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaClosureWitnessLedgerFields :
    MetaClosureWitnessLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaClosureWitnessLedgerUp.mk W K D A R H C P N => [W, K, D, A, R, H, C, P, N]

def metaClosureWitnessLedgerToEventFlow :
    MetaClosureWitnessLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaClosureWitnessLedgerUp.mk W K D A R H C P N =>
      [[BMark.b0],
        metaClosureWitnessLedgerEncodeBHist W,
        [BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaClosureWitnessLedgerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaClosureWitnessLedgerEncodeBHist N]

private def metaClosureWitnessLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => metaClosureWitnessLedgerRawAt n rest

private def metaClosureWitnessLedgerLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => metaClosureWitnessLedgerLengthEq n rest

def metaClosureWitnessLedgerFromEventFlow :
    EventFlow → Option MetaClosureWitnessLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match metaClosureWitnessLedgerLengthEq 18 flow with
      | true =>
          some
            (MetaClosureWitnessLedgerUp.mk
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 1 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 3 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 5 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 7 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 9 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 11 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 13 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 15 flow))
              (metaClosureWitnessLedgerDecodeBHist
                (metaClosureWitnessLedgerRawAt 17 flow)))
      | false => none

private theorem metaClosureWitnessLedger_round_trip :
    ∀ x : MetaClosureWitnessLedgerUp,
      metaClosureWitnessLedgerFromEventFlow
        (metaClosureWitnessLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W K D A R H C P N =>
      change
        some
          (MetaClosureWitnessLedgerUp.mk
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist W))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist K))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist D))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist A))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist R))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist H))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist C))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist P))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist N))) =
          some (MetaClosureWitnessLedgerUp.mk W K D A R H C P N)
      rw [metaClosureWitnessLedgerDecode_encode_bhist W,
        metaClosureWitnessLedgerDecode_encode_bhist K,
        metaClosureWitnessLedgerDecode_encode_bhist D,
        metaClosureWitnessLedgerDecode_encode_bhist A,
        metaClosureWitnessLedgerDecode_encode_bhist R,
        metaClosureWitnessLedgerDecode_encode_bhist H,
        metaClosureWitnessLedgerDecode_encode_bhist C,
        metaClosureWitnessLedgerDecode_encode_bhist P,
        metaClosureWitnessLedgerDecode_encode_bhist N]

private theorem metaClosureWitnessLedgerToEventFlow_injective
    {x y : MetaClosureWitnessLedgerUp} :
    metaClosureWitnessLedgerToEventFlow x =
      metaClosureWitnessLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaClosureWitnessLedgerFromEventFlow
          (metaClosureWitnessLedgerToEventFlow x) =
        metaClosureWitnessLedgerFromEventFlow
          (metaClosureWitnessLedgerToEventFlow y) :=
    congrArg metaClosureWitnessLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaClosureWitnessLedger_round_trip x).symm
      (Eq.trans hread (metaClosureWitnessLedger_round_trip y)))

private theorem metaClosureWitnessLedger_fields_faithful :
    ∀ x y : MetaClosureWitnessLedgerUp,
      metaClosureWitnessLedgerFields x =
        metaClosureWitnessLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W K D A R H C P N =>
      cases y with
      | mk W' K' D' A' R' H' C' P' N' =>
          cases hfields
          rfl

instance metaClosureWitnessLedgerBHistCarrier :
    BHistCarrier MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaClosureWitnessLedgerToEventFlow
  fromEventFlow := metaClosureWitnessLedgerFromEventFlow

instance metaClosureWitnessLedgerChapterTasteGate :
    ChapterTasteGate MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaClosureWitnessLedgerFromEventFlow
        (metaClosureWitnessLedgerToEventFlow x) = some x
    exact metaClosureWitnessLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaClosureWitnessLedgerToEventFlow_injective heq)

instance metaClosureWitnessLedgerFieldFaithful :
    FieldFaithful MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaClosureWitnessLedgerFields
  field_faithful := metaClosureWitnessLedger_fields_faithful

instance metaClosureWitnessLedgerNontrivial :
    Nontrivial MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaClosureWitnessLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaClosureWitnessLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetaClosureWitnessLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaClosureWitnessLedgerDecodeBHist
        (metaClosureWitnessLedgerEncodeBHist h) = h) ∧
      Nonempty (Nontrivial MetaClosureWitnessLedgerUp) ∧
        Nonempty (ChapterTasteGate MetaClosureWitnessLedgerUp) ∧
          Nonempty (FieldFaithful MetaClosureWitnessLedgerUp) ∧
            metaClosureWitnessLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨metaClosureWitnessLedgerDecode_encode_bhist,
      ⟨metaClosureWitnessLedgerNontrivial⟩,
      ⟨metaClosureWitnessLedgerChapterTasteGate⟩,
      ⟨metaClosureWitnessLedgerFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.MetaClosureWitnessLedgerUp.TasteGate
