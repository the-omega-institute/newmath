import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionFunctorUp : Type where
  | mk (L M U R E F H C P N : BHist) : LocatedCompletionFunctorUp
  deriving DecidableEq

def locatedCompletionFunctorFields : LocatedCompletionFunctorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionFunctorUp.mk L M U R E F H C P N => [L, M, U, R, E, F, H, C, P, N]

def locatedCompletionFunctorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionFunctorEncodeBHist h

def locatedCompletionFunctorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionFunctorDecodeBHist tail)

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionFunctorToEventFlow : LocatedCompletionFunctorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCompletionFunctorFields x).map locatedCompletionFunctorEncodeBHist

private def locatedCompletionFunctorRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => locatedCompletionFunctorRawAt n rest

def locatedCompletionFunctorFromEventFlow
    (flow : EventFlow) : Option LocatedCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompletionFunctorUp.mk
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 0 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 1 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 2 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 3 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 4 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 5 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 6 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 7 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 8 flow))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorRawAt 9 flow)))

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip
    (x : LocatedCompletionFunctorUp) :
    locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L M U R E F H C P N =>
      change
        some
          (LocatedCompletionFunctorUp.mk
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist L))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist M))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist U))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist R))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist E))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist F))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist H))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist C))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist P))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist N))) =
          some (LocatedCompletionFunctorUp.mk L M U R E F H C P N)
      rw [LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode L,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode M,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode U,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode E,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode F,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompletionFunctorUp} :
    locatedCompletionFunctorToEventFlow x = locatedCompletionFunctorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow x) =
        locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow y) :=
    congrArg locatedCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : LocatedCompletionFunctorUp,
      locatedCompletionFunctorFields x = locatedCompletionFunctorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 M1 U1 R1 E1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 M2 U2 R2 E2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedCompletionFunctorBHistCarrier : BHistCarrier LocatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionFunctorToEventFlow
  fromEventFlow := locatedCompletionFunctorFromEventFlow

instance locatedCompletionFunctorChapterTasteGate :
    ChapterTasteGate LocatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow x) = some x
    exact LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedCompletionFunctorFieldFaithful :
    FieldFaithful LocatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCompletionFunctorFields
  field_faithful := LocatedCompletionFunctorTasteGate_single_carrier_alignment_fields_faithful

theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedCompletionFunctorUp) ∧
      Nonempty (FieldFaithful LocatedCompletionFunctorUp) ∧
      locatedCompletionFunctorEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ h : BHist,
        locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionFunctorUp,
        locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨locatedCompletionFunctorChapterTasteGate⟩,
      ⟨locatedCompletionFunctorFieldFaithful⟩,
      rfl,
      LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode,
      LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.LocatedCompletionFunctorUp
