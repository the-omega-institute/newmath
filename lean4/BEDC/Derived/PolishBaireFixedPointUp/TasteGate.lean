import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolishBaireFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolishBaireFixedPointUp : Type where
  | mk :
      (polish baire ultrametric contraction iteration endpoint transport replay provenance
        localName : BHist) →
      PolishBaireFixedPointUp
  deriving DecidableEq

def polishBaireFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: polishBaireFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: polishBaireFixedPointEncodeBHist h

def polishBaireFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (polishBaireFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (polishBaireFixedPointDecodeBHist tail)

private theorem polishBaireFixedPoint_decode_encode_bhist :
    ∀ h : BHist,
      polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def polishBaireFixedPointFields : PolishBaireFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PolishBaireFixedPointUp.mk polish baire ultrametric contraction iteration endpoint
      transport replay provenance localName =>
      [polish, baire, ultrametric, contraction, iteration, endpoint, transport, replay,
        provenance, localName]

def polishBaireFixedPointToEventFlow : PolishBaireFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map polishBaireFixedPointEncodeBHist (polishBaireFixedPointFields x)

private def polishBaireFixedPointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => polishBaireFixedPointEventAtDefault index rest

def polishBaireFixedPointFromEventFlow : EventFlow → Option PolishBaireFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PolishBaireFixedPointUp.mk
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 0 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 1 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 2 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 3 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 4 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 5 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 6 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 7 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 8 ef))
        (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEventAtDefault 9 ef)))

private theorem polishBaireFixedPoint_round_trip :
    ∀ x : PolishBaireFixedPointUp,
      polishBaireFixedPointFromEventFlow (polishBaireFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk polish baire ultrametric contraction iteration endpoint transport replay provenance
      localName =>
      change
        some
          (PolishBaireFixedPointUp.mk
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist polish))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist baire))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist ultrametric))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist contraction))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist iteration))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist endpoint))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist transport))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist replay))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist provenance))
            (polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist localName))) =
          some
            (PolishBaireFixedPointUp.mk polish baire ultrametric contraction iteration
              endpoint transport replay provenance localName)
      rw [polishBaireFixedPoint_decode_encode_bhist polish,
        polishBaireFixedPoint_decode_encode_bhist baire,
        polishBaireFixedPoint_decode_encode_bhist ultrametric,
        polishBaireFixedPoint_decode_encode_bhist contraction,
        polishBaireFixedPoint_decode_encode_bhist iteration,
        polishBaireFixedPoint_decode_encode_bhist endpoint,
        polishBaireFixedPoint_decode_encode_bhist transport,
        polishBaireFixedPoint_decode_encode_bhist replay,
        polishBaireFixedPoint_decode_encode_bhist provenance,
        polishBaireFixedPoint_decode_encode_bhist localName]

private theorem polishBaireFixedPointToEventFlow_injective {x y : PolishBaireFixedPointUp} :
    polishBaireFixedPointToEventFlow x = polishBaireFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      polishBaireFixedPointFromEventFlow (polishBaireFixedPointToEventFlow x) =
        polishBaireFixedPointFromEventFlow (polishBaireFixedPointToEventFlow y) :=
    congrArg polishBaireFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (polishBaireFixedPoint_round_trip x).symm
      (Eq.trans hread (polishBaireFixedPoint_round_trip y)))

private theorem polishBaireFixedPoint_field_faithful :
    ∀ x y : PolishBaireFixedPointUp,
      polishBaireFixedPointFields x = polishBaireFixedPointFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk polish₁ baire₁ ultrametric₁ contraction₁ iteration₁ endpoint₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk polish₂ baire₂ ultrametric₂ contraction₂ iteration₂ endpoint₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance polishBaireFixedPointBHistCarrier : BHistCarrier PolishBaireFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := polishBaireFixedPointToEventFlow
  fromEventFlow := polishBaireFixedPointFromEventFlow

instance polishBaireFixedPointChapterTasteGate :
    ChapterTasteGate PolishBaireFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change polishBaireFixedPointFromEventFlow (polishBaireFixedPointToEventFlow x) = some x
    exact polishBaireFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (polishBaireFixedPointToEventFlow_injective heq)

instance polishBaireFixedPointFieldFaithful : FieldFaithful PolishBaireFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := polishBaireFixedPointFields
  field_faithful := polishBaireFixedPoint_field_faithful

instance polishBaireFixedPointNontrivial : Nontrivial PolishBaireFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PolishBaireFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PolishBaireFixedPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PolishBaireFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  polishBaireFixedPointChapterTasteGate

theorem PolishBaireFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        polishBaireFixedPointDecodeBHist (polishBaireFixedPointEncodeBHist h) = h) ∧
      (∀ x : PolishBaireFixedPointUp,
        polishBaireFixedPointFromEventFlow (polishBaireFixedPointToEventFlow x) = some x) ∧
        (∀ x y : PolishBaireFixedPointUp,
          polishBaireFixedPointToEventFlow x = polishBaireFixedPointToEventFlow y -> x = y) ∧
          polishBaireFixedPointEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : PolishBaireFixedPointUp,
              polishBaireFixedPointFields x = polishBaireFixedPointFields y -> x = y) ∧
              (∃ x y : PolishBaireFixedPointUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact polishBaireFixedPoint_decode_encode_bhist
  · constructor
    · exact polishBaireFixedPoint_round_trip
    · constructor
      · intro x y heq
        exact polishBaireFixedPointToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact polishBaireFixedPoint_field_faithful
          · exact
              ⟨PolishBaireFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                PolishBaireFixedPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.PolishBaireFixedPointUp
