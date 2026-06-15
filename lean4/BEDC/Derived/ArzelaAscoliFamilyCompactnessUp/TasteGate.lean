import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArzelaAscoliFamilyCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArzelaAscoliFamilyCompactnessUp : Type where
  | mk (A E K G M W B H C P N : BHist) : ArzelaAscoliFamilyCompactnessUp
  deriving DecidableEq

def arzelaAscoliFamilyCompactnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arzelaAscoliFamilyCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arzelaAscoliFamilyCompactnessEncodeBHist h

def arzelaAscoliFamilyCompactnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arzelaAscoliFamilyCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arzelaAscoliFamilyCompactnessDecodeBHist tail)

private theorem ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      arzelaAscoliFamilyCompactnessDecodeBHist
          (arzelaAscoliFamilyCompactnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arzelaAscoliFamilyCompactnessFields :
    ArzelaAscoliFamilyCompactnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArzelaAscoliFamilyCompactnessUp.mk A E K G M W B H C P N =>
      [A, E, K, G, M, W, B, H, C, P, N]

def arzelaAscoliFamilyCompactnessToEventFlow :
    ArzelaAscoliFamilyCompactnessUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (arzelaAscoliFamilyCompactnessFields x).map
      arzelaAscoliFamilyCompactnessEncodeBHist

private def arzelaAscoliFamilyCompactnessEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      arzelaAscoliFamilyCompactnessEventAtDefault index rest

def arzelaAscoliFamilyCompactnessFromEventFlow
    (ef : EventFlow) : Option ArzelaAscoliFamilyCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArzelaAscoliFamilyCompactnessUp.mk
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 0 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 1 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 2 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 3 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 4 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 5 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 6 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 7 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 8 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 9 ef))
      (arzelaAscoliFamilyCompactnessDecodeBHist
        (arzelaAscoliFamilyCompactnessEventAtDefault 10 ef)))

private theorem ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_round_trip :
    forall x : ArzelaAscoliFamilyCompactnessUp,
      arzelaAscoliFamilyCompactnessFromEventFlow
          (arzelaAscoliFamilyCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk A E K G M W B H C P N =>
      change
        some
          (ArzelaAscoliFamilyCompactnessUp.mk
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist A))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist E))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist K))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist G))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist M))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist W))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist B))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist H))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist C))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist P))
            (arzelaAscoliFamilyCompactnessDecodeBHist
              (arzelaAscoliFamilyCompactnessEncodeBHist N))) =
          some (ArzelaAscoliFamilyCompactnessUp.mk A E K G M W B H C P N)
      rw [ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode A,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode E,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode K,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode G,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode M,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode W,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode B,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode H,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode C,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode P,
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode N]

private theorem ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArzelaAscoliFamilyCompactnessUp} :
    arzelaAscoliFamilyCompactnessToEventFlow x =
      arzelaAscoliFamilyCompactnessToEventFlow y ->
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arzelaAscoliFamilyCompactnessFromEventFlow
          (arzelaAscoliFamilyCompactnessToEventFlow x) =
        arzelaAscoliFamilyCompactnessFromEventFlow
          (arzelaAscoliFamilyCompactnessToEventFlow y) :=
    congrArg arzelaAscoliFamilyCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_fields :
    forall x y : ArzelaAscoliFamilyCompactnessUp,
      arzelaAscoliFamilyCompactnessFields x =
        arzelaAscoliFamilyCompactnessFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 E1 K1 G1 M1 W1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 E2 K2 G2 M2 W2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance arzelaAscoliFamilyCompactnessBHistCarrier :
    BHistCarrier ArzelaAscoliFamilyCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arzelaAscoliFamilyCompactnessToEventFlow
  fromEventFlow := arzelaAscoliFamilyCompactnessFromEventFlow

instance arzelaAscoliFamilyCompactnessChapterTasteGate :
    ChapterTasteGate ArzelaAscoliFamilyCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arzelaAscoliFamilyCompactnessFromEventFlow
          (arzelaAscoliFamilyCompactnessToEventFlow x) =
        some x
    exact ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance arzelaAscoliFamilyCompactnessFieldFaithful :
    FieldFaithful ArzelaAscoliFamilyCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := arzelaAscoliFamilyCompactnessFields
  field_faithful :=
    ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_fields

instance arzelaAscoliFamilyCompactnessNontrivial :
    Nontrivial ArzelaAscoliFamilyCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArzelaAscoliFamilyCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ArzelaAscoliFamilyCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ArzelaAscoliFamilyCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  arzelaAscoliFamilyCompactnessChapterTasteGate

theorem ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment :
    (forall h : BHist,
      arzelaAscoliFamilyCompactnessDecodeBHist
          (arzelaAscoliFamilyCompactnessEncodeBHist h) =
        h) ∧
      (forall x : ArzelaAscoliFamilyCompactnessUp,
        arzelaAscoliFamilyCompactnessFromEventFlow
            (arzelaAscoliFamilyCompactnessToEventFlow x) =
          some x) ∧
        (forall x y : ArzelaAscoliFamilyCompactnessUp,
          arzelaAscoliFamilyCompactnessToEventFlow x =
            arzelaAscoliFamilyCompactnessToEventFlow y ->
          x = y) ∧
          arzelaAscoliFamilyCompactnessEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_decode,
      ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ArzelaAscoliFamilyCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.ArzelaAscoliFamilyCompactnessUp
