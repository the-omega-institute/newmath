import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedConsistencyAssemblyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedConsistencyAssemblyUp : Type where
  | mk (L T E F S O D R P N : BHist) : ClosedConsistencyAssemblyUp

def closedConsistencyAssemblyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedConsistencyAssemblyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedConsistencyAssemblyEncodeBHist h

def closedConsistencyAssemblyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedConsistencyAssemblyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedConsistencyAssemblyDecodeBHist tail)

private theorem closedConsistencyAssemblyDecode_encode_bhist :
    forall h : BHist,
      closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedConsistencyAssemblyFields : ClosedConsistencyAssemblyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedConsistencyAssemblyUp.mk L T E F S O D R P N => [L, T, E, F, S, O, D, R, P, N]

def closedConsistencyAssemblyToEventFlow : ClosedConsistencyAssemblyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedConsistencyAssemblyUp.mk L T E F S O D R P N =>
      [[BMark.b0],
        closedConsistencyAssemblyEncodeBHist L,
        [BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedConsistencyAssemblyEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closedConsistencyAssemblyEncodeBHist N]

private def closedConsistencyAssemblyRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => closedConsistencyAssemblyRawAt n rest

private def closedConsistencyAssemblyLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => closedConsistencyAssemblyLengthEq n rest

def closedConsistencyAssemblyFromEventFlow : EventFlow -> Option ClosedConsistencyAssemblyUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match closedConsistencyAssemblyLengthEq 20 flow with
      | true =>
          some
            (ClosedConsistencyAssemblyUp.mk
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 1 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 3 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 5 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 7 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 9 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 11 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 13 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 15 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 17 flow))
              (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyRawAt 19 flow)))
      | false => none

private theorem closedConsistencyAssembly_round_trip :
    forall x : ClosedConsistencyAssemblyUp,
      closedConsistencyAssemblyFromEventFlow
        (closedConsistencyAssemblyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L T E F S O D R P N =>
      change
        some
          (ClosedConsistencyAssemblyUp.mk
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist L))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist T))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist E))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist F))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist S))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist O))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist D))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist R))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist P))
            (closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist N))) =
          some (ClosedConsistencyAssemblyUp.mk L T E F S O D R P N)
      rw [closedConsistencyAssemblyDecode_encode_bhist L,
        closedConsistencyAssemblyDecode_encode_bhist T,
        closedConsistencyAssemblyDecode_encode_bhist E,
        closedConsistencyAssemblyDecode_encode_bhist F,
        closedConsistencyAssemblyDecode_encode_bhist S,
        closedConsistencyAssemblyDecode_encode_bhist O,
        closedConsistencyAssemblyDecode_encode_bhist D,
        closedConsistencyAssemblyDecode_encode_bhist R,
        closedConsistencyAssemblyDecode_encode_bhist P,
        closedConsistencyAssemblyDecode_encode_bhist N]

private theorem closedConsistencyAssemblyToEventFlow_injective
    {x y : ClosedConsistencyAssemblyUp} :
    closedConsistencyAssemblyToEventFlow x = closedConsistencyAssemblyToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow x) =
        closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow y) :=
    congrArg closedConsistencyAssemblyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedConsistencyAssembly_round_trip x).symm
      (Eq.trans hread (closedConsistencyAssembly_round_trip y)))

private theorem closedConsistencyAssembly_field_faithful :
    forall x y : ClosedConsistencyAssemblyUp,
      closedConsistencyAssemblyFields x = closedConsistencyAssemblyFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 T1 E1 F1 S1 O1 D1 R1 P1 N1 =>
      cases y with
      | mk L2 T2 E2 F2 S2 O2 D2 R2 P2 N2 =>
          cases hfields
          rfl

instance closedConsistencyAssemblyBHistCarrier : BHistCarrier ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedConsistencyAssemblyToEventFlow
  fromEventFlow := closedConsistencyAssemblyFromEventFlow

instance closedConsistencyAssemblyChapterTasteGate :
    ChapterTasteGate ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedConsistencyAssemblyFromEventFlow
        (closedConsistencyAssemblyToEventFlow x) = some x
    exact closedConsistencyAssembly_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedConsistencyAssemblyToEventFlow_injective heq)

instance closedConsistencyAssemblyFieldFaithful :
    FieldFaithful ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedConsistencyAssemblyFields
  field_faithful := closedConsistencyAssembly_field_faithful

instance closedConsistencyAssemblyNontrivial : Nontrivial ClosedConsistencyAssemblyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedConsistencyAssemblyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedConsistencyAssemblyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedConsistencyAssemblyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedConsistencyAssemblyChapterTasteGate

theorem ClosedConsistencyAssemblyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedConsistencyAssemblyDecodeBHist (closedConsistencyAssemblyEncodeBHist h) = h) ∧
      (∀ x : ClosedConsistencyAssemblyUp,
        closedConsistencyAssemblyFromEventFlow (closedConsistencyAssemblyToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedConsistencyAssemblyUp,
          closedConsistencyAssemblyToEventFlow x = closedConsistencyAssemblyToEventFlow y ->
            x = y) ∧
          closedConsistencyAssemblyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨closedConsistencyAssemblyDecode_encode_bhist,
      closedConsistencyAssembly_round_trip,
      (fun _ _ heq => closedConsistencyAssemblyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClosedConsistencyAssemblyUp
