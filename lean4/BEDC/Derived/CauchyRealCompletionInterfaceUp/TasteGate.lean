import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealCompletionInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealCompletionInterfaceUp : Type where
  | mk (D S R B T H C P N : BHist) : CauchyRealCompletionInterfaceUp
  deriving DecidableEq

def cauchyRealCompletionInterfaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealCompletionInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealCompletionInterfaceEncodeBHist h

def cauchyRealCompletionInterfaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealCompletionInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealCompletionInterfaceDecodeBHist tail)

private theorem CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealCompletionInterfaceFields : CauchyRealCompletionInterfaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealCompletionInterfaceUp.mk D S R B T H C P N => [D, S, R, B, T, H, C, P, N]

def cauchyRealCompletionInterfaceToEventFlow :
    CauchyRealCompletionInterfaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyRealCompletionInterfaceEncodeBHist
      (cauchyRealCompletionInterfaceFields x)

private def cauchyRealCompletionInterfaceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealCompletionInterfaceEventAtDefault index rest

def cauchyRealCompletionInterfaceFromEventFlow
    (ef : EventFlow) : Option CauchyRealCompletionInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealCompletionInterfaceUp.mk
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 0 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 1 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 2 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 3 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 4 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 5 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 6 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 7 ef))
      (cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEventAtDefault 8 ef)))

private theorem CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyRealCompletionInterfaceUp,
      cauchyRealCompletionInterfaceFromEventFlow
        (cauchyRealCompletionInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R B T H C P N =>
      change
        some
          (CauchyRealCompletionInterfaceUp.mk
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist D))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist S))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist R))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist B))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist T))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist H))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist C))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist P))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist N))) =
          some (CauchyRealCompletionInterfaceUp.mk D S R B T H C P N)
      rw [CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode D,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode S,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode R,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode B,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode T,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode H,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode C,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode P,
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode N]

private theorem CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealCompletionInterfaceUp} :
    cauchyRealCompletionInterfaceToEventFlow x =
      cauchyRealCompletionInterfaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow x) =
        cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow y) :=
    congrArg cauchyRealCompletionInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_fields :
    forall x y : CauchyRealCompletionInterfaceUp,
      cauchyRealCompletionInterfaceFields x = cauchyRealCompletionInterfaceFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 B1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 B2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyRealCompletionInterfaceBHistCarrier :
    BHistCarrier CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealCompletionInterfaceToEventFlow
  fromEventFlow := cauchyRealCompletionInterfaceFromEventFlow

instance cauchyRealCompletionInterfaceChapterTasteGate :
    ChapterTasteGate CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyRealCompletionInterfaceFromEventFlow
        (cauchyRealCompletionInterfaceToEventFlow x) = some x
    exact CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchyRealCompletionInterfaceFieldFaithful :
    FieldFaithful CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealCompletionInterfaceFields
  field_faithful := CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_fields

instance cauchyRealCompletionInterfaceNontrivial :
    Nontrivial CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealCompletionInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealCompletionInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEncodeBHist h) = h) /\
      (forall x : CauchyRealCompletionInterfaceUp,
        cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow x) = some x) /\
        (forall x y : CauchyRealCompletionInterfaceUp,
          cauchyRealCompletionInterfaceToEventFlow x =
            cauchyRealCompletionInterfaceToEventFlow y -> x = y) /\
          cauchyRealCompletionInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_decode,
      CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

theorem CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEncodeBHist h) = h) /\
      (forall x : CauchyRealCompletionInterfaceUp,
        cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow x) = some x) /\
        (forall x y : CauchyRealCompletionInterfaceUp,
          cauchyRealCompletionInterfaceToEventFlow x =
            cauchyRealCompletionInterfaceToEventFlow y -> x = y) /\
          cauchyRealCompletionInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact CauchyRealCompletionInterfaceUpTasteGate_single_carrier_alignment

end BEDC.Derived.CauchyRealCompletionInterfaceUp
