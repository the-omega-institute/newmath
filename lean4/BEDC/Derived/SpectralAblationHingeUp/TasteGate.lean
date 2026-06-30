import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpectralAblationHingeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpectralAblationHingeUp : Type where
  | mk (D K L O T R H C P N : BHist) : SpectralAblationHingeUp
  deriving DecidableEq

def spectralAblationHingeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spectralAblationHingeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spectralAblationHingeEncodeBHist h

def spectralAblationHingeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spectralAblationHingeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spectralAblationHingeDecodeBHist tail)

private theorem SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      spectralAblationHingeDecodeBHist
          (spectralAblationHingeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def spectralAblationHingeFields : SpectralAblationHingeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpectralAblationHingeUp.mk D K L O T R H C P N =>
      [D, K, L, O, T, R, H, C, P, N]

def spectralAblationHingeToEventFlow : SpectralAblationHingeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (spectralAblationHingeFields x).map spectralAblationHingeEncodeBHist

private def spectralAblationHingeEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      spectralAblationHingeEventAtDefault index rest

def spectralAblationHingeFromEventFlow :
    EventFlow -> Option SpectralAblationHingeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SpectralAblationHingeUp.mk
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 0 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 1 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 2 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 3 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 4 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 5 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 6 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 7 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 8 ef))
        (spectralAblationHingeDecodeBHist (spectralAblationHingeEventAtDefault 9 ef)))

private theorem SpectralAblationHingeTasteGate_single_carrier_alignment_round_trip
    (x : SpectralAblationHingeUp) :
    spectralAblationHingeFromEventFlow (spectralAblationHingeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D K L O T R H C P N =>
      change
        some
          (SpectralAblationHingeUp.mk
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist D))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist K))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist L))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist O))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist T))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist R))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist H))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist C))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist P))
            (spectralAblationHingeDecodeBHist (spectralAblationHingeEncodeBHist N))) =
          some (SpectralAblationHingeUp.mk D K L O T R H C P N)
      rw [SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode D,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode K,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode L,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode O,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode T,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode R,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode H,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode C,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode P,
        SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode N]

private theorem SpectralAblationHingeTasteGate_single_carrier_alignment_injective
    {x y : SpectralAblationHingeUp} :
    spectralAblationHingeToEventFlow x =
        spectralAblationHingeToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spectralAblationHingeFromEventFlow (spectralAblationHingeToEventFlow x) =
        spectralAblationHingeFromEventFlow (spectralAblationHingeToEventFlow y) :=
    congrArg spectralAblationHingeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SpectralAblationHingeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SpectralAblationHingeTasteGate_single_carrier_alignment_round_trip y)))

private theorem SpectralAblationHingeTasteGate_single_carrier_alignment_fields :
    forall x y : SpectralAblationHingeUp,
      spectralAblationHingeFields x =
        spectralAblationHingeFields y ->
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 K1 L1 O1 T1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 K2 L2 O2 T2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance spectralAblationHingeBHistCarrier :
    BHistCarrier SpectralAblationHingeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spectralAblationHingeToEventFlow
  fromEventFlow := spectralAblationHingeFromEventFlow

instance spectralAblationHingeChapterTasteGate :
    ChapterTasteGate SpectralAblationHingeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      spectralAblationHingeFromEventFlow (spectralAblationHingeToEventFlow x) =
        some x
    exact SpectralAblationHingeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SpectralAblationHingeTasteGate_single_carrier_alignment_injective heq)

instance spectralAblationHingeFieldFaithful :
    FieldFaithful SpectralAblationHingeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := spectralAblationHingeFields
  field_faithful := SpectralAblationHingeTasteGate_single_carrier_alignment_fields

instance spectralAblationHingeNontrivial :
    Nontrivial SpectralAblationHingeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SpectralAblationHingeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SpectralAblationHingeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SpectralAblationHingeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  spectralAblationHingeChapterTasteGate

theorem SpectralAblationHingeTasteGate_single_carrier_alignment :
    (forall h : BHist,
      spectralAblationHingeDecodeBHist
          (spectralAblationHingeEncodeBHist h) =
        h) ∧
      (forall x : SpectralAblationHingeUp,
        spectralAblationHingeFromEventFlow (spectralAblationHingeToEventFlow x) =
          some x) ∧
        (forall x y : SpectralAblationHingeUp,
          spectralAblationHingeToEventFlow x =
              spectralAblationHingeToEventFlow y ->
            x = y) ∧
          (forall x y : SpectralAblationHingeUp,
            spectralAblationHingeFields x =
                spectralAblationHingeFields y ->
              x = y) ∧
            (exists x y : SpectralAblationHingeUp, x ≠ y) ∧
              spectralAblationHingeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SpectralAblationHingeTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact SpectralAblationHingeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact SpectralAblationHingeTasteGate_single_carrier_alignment_injective heq
      · constructor
        · exact SpectralAblationHingeTasteGate_single_carrier_alignment_fields
        · constructor
          · exact
              ⟨SpectralAblationHingeUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                SpectralAblationHingeUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          · rfl

end BEDC.Derived.SpectralAblationHingeUp
