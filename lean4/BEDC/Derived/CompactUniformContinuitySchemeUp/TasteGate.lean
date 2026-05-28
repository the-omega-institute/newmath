import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformContinuitySchemeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformContinuitySchemeUp : Type where
  | mk (X Y F E P M Q T G H R S N : BHist) : CompactUniformContinuitySchemeUp
  deriving DecidableEq

def compactUniformContinuitySchemeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformContinuitySchemeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformContinuitySchemeEncodeBHist h

def compactUniformContinuitySchemeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformContinuitySchemeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformContinuitySchemeDecodeBHist tail)

private theorem compactUniformContinuityScheme_decode_encode :
    ∀ h : BHist,
      compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformContinuitySchemeFields :
    CompactUniformContinuitySchemeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformContinuitySchemeUp.mk X Y F E P M Q T G H R S N =>
      [X, Y, F, E, P, M, Q, T, G, H, R, S, N]

def compactUniformContinuitySchemeToEventFlow :
    CompactUniformContinuitySchemeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactUniformContinuitySchemeFields x).map
        compactUniformContinuitySchemeEncodeBHist

private def compactUniformContinuitySchemeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformContinuitySchemeEventAt index rest

def compactUniformContinuitySchemeFromEventFlow :
    EventFlow → Option CompactUniformContinuitySchemeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactUniformContinuitySchemeUp.mk
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 0 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 1 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 2 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 3 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 4 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 5 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 6 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 7 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 8 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 9 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 10 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 11 ef))
        (compactUniformContinuitySchemeDecodeBHist
          (compactUniformContinuitySchemeEventAt 12 ef)))

private theorem compactUniformContinuityScheme_round_trip
    (x : CompactUniformContinuitySchemeUp) :
    compactUniformContinuitySchemeFromEventFlow
        (compactUniformContinuitySchemeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y F E P M Q T G H R S N =>
      change
        some
          (CompactUniformContinuitySchemeUp.mk
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist X))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist Y))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist F))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist E))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist P))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist M))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist Q))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist T))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist G))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist H))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist R))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist S))
            (compactUniformContinuitySchemeDecodeBHist
              (compactUniformContinuitySchemeEncodeBHist N))) =
          some (CompactUniformContinuitySchemeUp.mk X Y F E P M Q T G H R S N)
      rw [compactUniformContinuityScheme_decode_encode X,
        compactUniformContinuityScheme_decode_encode Y,
        compactUniformContinuityScheme_decode_encode F,
        compactUniformContinuityScheme_decode_encode E,
        compactUniformContinuityScheme_decode_encode P,
        compactUniformContinuityScheme_decode_encode M,
        compactUniformContinuityScheme_decode_encode Q,
        compactUniformContinuityScheme_decode_encode T,
        compactUniformContinuityScheme_decode_encode G,
        compactUniformContinuityScheme_decode_encode H,
        compactUniformContinuityScheme_decode_encode R,
        compactUniformContinuityScheme_decode_encode S,
        compactUniformContinuityScheme_decode_encode N]

private theorem CompactUniformContinuitySchemeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformContinuitySchemeUp} :
    compactUniformContinuitySchemeToEventFlow x =
        compactUniformContinuitySchemeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      compactUniformContinuitySchemeFromEventFlow
          (compactUniformContinuitySchemeToEventFlow x) =
        compactUniformContinuitySchemeFromEventFlow
          (compactUniformContinuitySchemeToEventFlow y) :=
    congrArg compactUniformContinuitySchemeFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (compactUniformContinuityScheme_round_trip x).symm
      (Eq.trans hread (compactUniformContinuityScheme_round_trip y)))

private theorem compactUniformContinuityScheme_field_faithful :
    ∀ x y : CompactUniformContinuitySchemeUp,
      compactUniformContinuitySchemeFields x =
          compactUniformContinuitySchemeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 F1 E1 P1 M1 Q1 T1 G1 H1 R1 S1 N1 =>
      cases y with
      | mk X2 Y2 F2 E2 P2 M2 Q2 T2 G2 H2 R2 S2 N2 =>
          cases hfields
          rfl

instance compactUniformContinuitySchemeBHistCarrier :
    BHistCarrier CompactUniformContinuitySchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformContinuitySchemeToEventFlow
  fromEventFlow := compactUniformContinuitySchemeFromEventFlow

instance compactUniformContinuitySchemeChapterTasteGate :
    ChapterTasteGate CompactUniformContinuitySchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformContinuitySchemeFromEventFlow
          (compactUniformContinuitySchemeToEventFlow x) =
        some x
    exact compactUniformContinuityScheme_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformContinuitySchemeTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance compactUniformContinuitySchemeFieldFaithful :
    FieldFaithful CompactUniformContinuitySchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformContinuitySchemeFields
  field_faithful := compactUniformContinuityScheme_field_faithful

instance compactUniformContinuitySchemeNontrivial :
    Nontrivial CompactUniformContinuitySchemeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformContinuitySchemeUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformContinuitySchemeUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def CompactUniformContinuitySchemeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompactUniformContinuitySchemeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformContinuitySchemeChapterTasteGate

theorem CompactUniformContinuitySchemeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformContinuitySchemeDecodeBHist
        (compactUniformContinuitySchemeEncodeBHist h) = h) ∧
      compactUniformContinuitySchemeFields
        (CompactUniformContinuitySchemeUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact compactUniformContinuityScheme_decode_encode
  · rfl

end BEDC.Derived.CompactUniformContinuitySchemeUp
