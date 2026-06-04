import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PackingNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PackingNumberUp : Type where
  | mk (X eps U D B H C P N : BHist) : PackingNumberUp
  deriving DecidableEq

def packingNumberEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: packingNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: packingNumberEncodeBHist h

def packingNumberDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (packingNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (packingNumberDecodeBHist tail)

private theorem packingNumberDecode_encode :
    forall h : BHist, packingNumberDecodeBHist (packingNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def packingNumberFields : PackingNumberUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PackingNumberUp.mk X eps U D B H C P N => [X, eps, U, D, B, H, C, P, N]

def packingNumberToEventFlow : PackingNumberUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (packingNumberFields x).map packingNumberEncodeBHist

private def packingNumberEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => packingNumberEventAt index rest

def packingNumberFromEventFlow : EventFlow -> Option PackingNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PackingNumberUp.mk
        (packingNumberDecodeBHist (packingNumberEventAt 0 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 1 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 2 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 3 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 4 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 5 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 6 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 7 ef))
        (packingNumberDecodeBHist (packingNumberEventAt 8 ef)))

private theorem packingNumber_round_trip :
    forall x : PackingNumberUp,
      packingNumberFromEventFlow (packingNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X eps U D B H C P N =>
      change
        some
            (PackingNumberUp.mk
              (packingNumberDecodeBHist (packingNumberEncodeBHist X))
              (packingNumberDecodeBHist (packingNumberEncodeBHist eps))
              (packingNumberDecodeBHist (packingNumberEncodeBHist U))
              (packingNumberDecodeBHist (packingNumberEncodeBHist D))
              (packingNumberDecodeBHist (packingNumberEncodeBHist B))
              (packingNumberDecodeBHist (packingNumberEncodeBHist H))
              (packingNumberDecodeBHist (packingNumberEncodeBHist C))
              (packingNumberDecodeBHist (packingNumberEncodeBHist P))
              (packingNumberDecodeBHist (packingNumberEncodeBHist N))) =
          some (PackingNumberUp.mk X eps U D B H C P N)
      rw [packingNumberDecode_encode X, packingNumberDecode_encode eps,
        packingNumberDecode_encode U, packingNumberDecode_encode D,
        packingNumberDecode_encode B, packingNumberDecode_encode H,
        packingNumberDecode_encode C, packingNumberDecode_encode P,
        packingNumberDecode_encode N]

private theorem packingNumberToEventFlow_injective {x y : PackingNumberUp} :
    packingNumberToEventFlow x = packingNumberToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packingNumberFromEventFlow (packingNumberToEventFlow x) =
        packingNumberFromEventFlow (packingNumberToEventFlow y) :=
    congrArg packingNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (packingNumber_round_trip x).symm
      (Eq.trans hread (packingNumber_round_trip y)))

private theorem packingNumber_field_faithful :
    forall x y : PackingNumberUp, packingNumberFields x = packingNumberFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 eps1 U1 D1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 eps2 U2 D2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance packingNumberBHistCarrier : BHistCarrier PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := packingNumberToEventFlow
  fromEventFlow := packingNumberFromEventFlow

instance packingNumberChapterTasteGate : ChapterTasteGate PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change packingNumberFromEventFlow (packingNumberToEventFlow x) = some x
    exact packingNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (packingNumberToEventFlow_injective heq)

instance packingNumberFieldFaithful : FieldFaithful PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := packingNumberFields
  field_faithful := packingNumber_field_faithful

instance packingNumberNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackingNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PackingNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PackingNumberTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PackingNumberUp) ∧
      Nonempty (FieldFaithful PackingNumberUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PackingNumberUp) ∧
      (forall h : BHist, packingNumberDecodeBHist (packingNumberEncodeBHist h) = h) ∧
      (forall x : PackingNumberUp,
        packingNumberFromEventFlow (packingNumberToEventFlow x) = some x) ∧
      (forall x y : PackingNumberUp,
        packingNumberToEventFlow x = packingNumberToEventFlow y -> x = y) ∧
      packingNumberEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨packingNumberChapterTasteGate⟩
  constructor
  · exact ⟨packingNumberFieldFaithful⟩
  constructor
  · exact ⟨packingNumberNontrivial⟩
  constructor
  · exact packingNumberDecode_encode
  constructor
  · exact packingNumber_round_trip
  constructor
  · intro x y heq
    exact packingNumberToEventFlow_injective heq
  · rfl

end BEDC.Derived.PackingNumberUp
