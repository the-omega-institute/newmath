import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TernaryExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TernaryExpansionUp : Type where
  | mk
      (digits windows placeValue dyadicComparison regularHandoff retainedPrefix realSeal
        transport replay provenance name : BHist) :
      TernaryExpansionUp
  deriving DecidableEq

def ternaryExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ternaryExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ternaryExpansionEncodeBHist h

def ternaryExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ternaryExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ternaryExpansionDecodeBHist tail)

private theorem ternaryExpansion_decode_encode_bhist :
    ∀ h : BHist, ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ternaryExpansionFields : TernaryExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TernaryExpansionUp.mk digits windows placeValue dyadicComparison regularHandoff
      retainedPrefix realSeal transport replay provenance name =>
      [digits, windows, placeValue, dyadicComparison, regularHandoff, retainedPrefix,
        realSeal, transport, replay, provenance, name]

def ternaryExpansionToEventFlow : TernaryExpansionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ternaryExpansionFields x).map ternaryExpansionEncodeBHist

private def ternaryExpansionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ternaryExpansionEventAtDefault index rest

def ternaryExpansionFromEventFlow (ef : EventFlow) : Option TernaryExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TernaryExpansionUp.mk
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 0 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 1 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 2 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 3 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 4 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 5 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 6 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 7 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 8 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 9 ef))
      (ternaryExpansionDecodeBHist (ternaryExpansionEventAtDefault 10 ef)))

private theorem ternaryExpansion_round_trip :
    ∀ x : TernaryExpansionUp,
      ternaryExpansionFromEventFlow (ternaryExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk digits windows placeValue dyadicComparison regularHandoff retainedPrefix realSeal
      transport replay provenance name =>
      change
        some
          (TernaryExpansionUp.mk
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist digits))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist windows))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist placeValue))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist dyadicComparison))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist regularHandoff))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist retainedPrefix))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist realSeal))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist transport))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist replay))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist provenance))
            (ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist name))) =
          some
            (TernaryExpansionUp.mk digits windows placeValue dyadicComparison regularHandoff
              retainedPrefix realSeal transport replay provenance name)
      rw [ternaryExpansion_decode_encode_bhist digits,
        ternaryExpansion_decode_encode_bhist windows,
        ternaryExpansion_decode_encode_bhist placeValue,
        ternaryExpansion_decode_encode_bhist dyadicComparison,
        ternaryExpansion_decode_encode_bhist regularHandoff,
        ternaryExpansion_decode_encode_bhist retainedPrefix,
        ternaryExpansion_decode_encode_bhist realSeal,
        ternaryExpansion_decode_encode_bhist transport,
        ternaryExpansion_decode_encode_bhist replay,
        ternaryExpansion_decode_encode_bhist provenance,
        ternaryExpansion_decode_encode_bhist name]

private theorem TernaryExpansionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TernaryExpansionUp} :
    ternaryExpansionToEventFlow x = ternaryExpansionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ternaryExpansionFromEventFlow (ternaryExpansionToEventFlow x) =
        ternaryExpansionFromEventFlow (ternaryExpansionToEventFlow y) :=
    congrArg ternaryExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ternaryExpansion_round_trip x).symm
      (Eq.trans hread (ternaryExpansion_round_trip y)))

instance ternaryExpansionBHistCarrier : BHistCarrier TernaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ternaryExpansionToEventFlow
  fromEventFlow := ternaryExpansionFromEventFlow

instance ternaryExpansionChapterTasteGate : ChapterTasteGate TernaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ternaryExpansionFromEventFlow (ternaryExpansionToEventFlow x) = some x
    exact ternaryExpansion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TernaryExpansionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ternaryExpansionNontrivial : Nontrivial TernaryExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TernaryExpansionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TernaryExpansionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TernaryExpansionTasteGate_single_carrier_alignment :
    (∀ h : BHist, ternaryExpansionDecodeBHist (ternaryExpansionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier TernaryExpansionUp) ∧
        Nonempty (ChapterTasteGate TernaryExpansionUp) ∧
          ternaryExpansionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ternaryExpansion_decode_encode_bhist,
      ⟨⟨ternaryExpansionBHistCarrier⟩, ⟨⟨ternaryExpansionChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.TernaryExpansionUp
