import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoetherNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NoetherNormalizationUp : Type where
  | mk (F R P A G C I M H Q K : BHist) : NoetherNormalizationUp
  deriving DecidableEq

def noetherNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noetherNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noetherNormalizationEncodeBHist h

def noetherNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noetherNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noetherNormalizationDecodeBHist tail)

private theorem noetherNormalization_decode_encode_bhist :
    ∀ h : BHist, noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def noetherNormalizationToEventFlow : NoetherNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NoetherNormalizationUp.mk F R P A G C I M H Q K =>
      [noetherNormalizationEncodeBHist F, noetherNormalizationEncodeBHist R,
        noetherNormalizationEncodeBHist P, noetherNormalizationEncodeBHist A,
        noetherNormalizationEncodeBHist G, noetherNormalizationEncodeBHist C,
        noetherNormalizationEncodeBHist I, noetherNormalizationEncodeBHist M,
        noetherNormalizationEncodeBHist H, noetherNormalizationEncodeBHist Q,
        noetherNormalizationEncodeBHist K]

private def noetherNormalizationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => noetherNormalizationRawAt n rest

private def noetherNormalizationLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => noetherNormalizationLengthEq n rest

def noetherNormalizationFromEventFlow : EventFlow → Option NoetherNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match noetherNormalizationLengthEq 11 flow with
      | true =>
          some
            (NoetherNormalizationUp.mk
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 0 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 1 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 2 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 3 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 4 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 5 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 6 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 7 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 8 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 9 flow))
              (noetherNormalizationDecodeBHist (noetherNormalizationRawAt 10 flow)))
      | false => none

private theorem noetherNormalization_round_trip :
    ∀ x : NoetherNormalizationUp,
      noetherNormalizationFromEventFlow (noetherNormalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F R P A G C I M H Q K =>
      change
        some
          (NoetherNormalizationUp.mk
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist F))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist R))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist P))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist A))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist G))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist C))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist I))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist M))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist H))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist Q))
            (noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist K))) =
          some (NoetherNormalizationUp.mk F R P A G C I M H Q K)
      rw [noetherNormalization_decode_encode_bhist F,
        noetherNormalization_decode_encode_bhist R,
        noetherNormalization_decode_encode_bhist P,
        noetherNormalization_decode_encode_bhist A,
        noetherNormalization_decode_encode_bhist G,
        noetherNormalization_decode_encode_bhist C,
        noetherNormalization_decode_encode_bhist I,
        noetherNormalization_decode_encode_bhist M,
        noetherNormalization_decode_encode_bhist H,
        noetherNormalization_decode_encode_bhist Q,
        noetherNormalization_decode_encode_bhist K]

private theorem noetherNormalizationToEventFlow_injective {x y : NoetherNormalizationUp} :
    noetherNormalizationToEventFlow x = noetherNormalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noetherNormalizationFromEventFlow (noetherNormalizationToEventFlow x) =
        noetherNormalizationFromEventFlow (noetherNormalizationToEventFlow y) :=
    congrArg noetherNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (noetherNormalization_round_trip x).symm
      (Eq.trans hread (noetherNormalization_round_trip y)))

instance noetherNormalizationBHistCarrier : BHistCarrier NoetherNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noetherNormalizationToEventFlow
  fromEventFlow := noetherNormalizationFromEventFlow

instance noetherNormalizationChapterTasteGate : ChapterTasteGate NoetherNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noetherNormalizationFromEventFlow (noetherNormalizationToEventFlow x) = some x
    exact noetherNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (noetherNormalizationToEventFlow_injective heq)

theorem NoetherNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, noetherNormalizationDecodeBHist (noetherNormalizationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NoetherNormalizationUp) ∧
        Nonempty (ChapterTasteGate NoetherNormalizationUp) ∧
          noetherNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨noetherNormalization_decode_encode_bhist,
      ⟨⟨noetherNormalizationBHistCarrier⟩,
        ⟨⟨noetherNormalizationChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.NoetherNormalizationUp
