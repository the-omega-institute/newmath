import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySpaceUp : Type where
  | mk (F U R Q T H C P N : BHist) : CauchySpaceUp
  deriving DecidableEq

def cauchySpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySpaceEncodeBHist h

def cauchySpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySpaceDecodeBHist tail)

private theorem CauchySpaceTasteGate_single_carrier_alignment_decode :
    forall h : BHist, cauchySpaceDecodeBHist (cauchySpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySpaceFields : CauchySpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySpaceUp.mk F U R Q T H C P N => [F, U, R, Q, T, H, C, P, N]

def cauchySpaceToEventFlow : CauchySpaceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchySpaceFields x).map cauchySpaceEncodeBHist

private def cauchySpaceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySpaceEventAtDefault index rest

def cauchySpaceFromEventFlow (ef : EventFlow) : Option CauchySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySpaceUp.mk
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 0 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 1 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 2 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 3 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 4 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 5 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 6 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 7 ef))
      (cauchySpaceDecodeBHist (cauchySpaceEventAtDefault 8 ef)))

private theorem CauchySpaceTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchySpaceUp, cauchySpaceFromEventFlow (cauchySpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F U R Q T H C P N =>
      change
        some
          (CauchySpaceUp.mk
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist F))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist U))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist R))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist Q))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist T))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist H))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist C))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist P))
            (cauchySpaceDecodeBHist (cauchySpaceEncodeBHist N))) =
          some (CauchySpaceUp.mk F U R Q T H C P N)
      rw [CauchySpaceTasteGate_single_carrier_alignment_decode F,
        CauchySpaceTasteGate_single_carrier_alignment_decode U,
        CauchySpaceTasteGate_single_carrier_alignment_decode R,
        CauchySpaceTasteGate_single_carrier_alignment_decode Q,
        CauchySpaceTasteGate_single_carrier_alignment_decode T,
        CauchySpaceTasteGate_single_carrier_alignment_decode H,
        CauchySpaceTasteGate_single_carrier_alignment_decode C,
        CauchySpaceTasteGate_single_carrier_alignment_decode P,
        CauchySpaceTasteGate_single_carrier_alignment_decode N]

private theorem CauchySpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySpaceUp} :
    cauchySpaceToEventFlow x = cauchySpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySpaceFromEventFlow (cauchySpaceToEventFlow x) =
        cauchySpaceFromEventFlow (cauchySpaceToEventFlow y) :=
    congrArg cauchySpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchySpaceTasteGate_single_carrier_alignment_fields :
    forall x y : CauchySpaceUp, cauchySpaceFields x = cauchySpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 U1 R1 Q1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 U2 R2 Q2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchySpaceBHistCarrier : BHistCarrier CauchySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySpaceToEventFlow
  fromEventFlow := cauchySpaceFromEventFlow

instance cauchySpaceChapterTasteGate : ChapterTasteGate CauchySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySpaceFromEventFlow (cauchySpaceToEventFlow x) = some x
    exact CauchySpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchySpaceFieldFaithful : FieldFaithful CauchySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySpaceFields
  field_faithful := CauchySpaceTasteGate_single_carrier_alignment_fields

instance cauchySpaceNontrivial : Nontrivial CauchySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySpaceChapterTasteGate

theorem CauchySpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchySpaceDecodeBHist (cauchySpaceEncodeBHist h) = h) /\
      (forall x : CauchySpaceUp, cauchySpaceFromEventFlow (cauchySpaceToEventFlow x) = some x) /\
        (forall x y : CauchySpaceUp, cauchySpaceToEventFlow x = cauchySpaceToEventFlow y -> x = y) /\
          cauchySpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨CauchySpaceTasteGate_single_carrier_alignment_decode,
      CauchySpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchySpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySpaceUp
