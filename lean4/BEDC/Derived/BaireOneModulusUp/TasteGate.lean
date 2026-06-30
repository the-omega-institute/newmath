import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireOneModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireOneModulusUp : Type where
  | mk (S A T O W M R E H C P N : BHist) : BaireOneModulusUp
  deriving DecidableEq

def baireOneModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireOneModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireOneModulusEncodeBHist h

def baireOneModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireOneModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireOneModulusDecodeBHist tail)

private theorem BaireOneModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireOneModulusDecodeBHist (baireOneModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireOneModulusFields : BaireOneModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireOneModulusUp.mk S A T O W M R E H C P N => [S, A, T, O, W, M, R, E, H, C, P, N]

def baireOneModulusToEventFlow : BaireOneModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireOneModulusFields x).map baireOneModulusEncodeBHist

private def baireOneModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireOneModulusEventAtDefault index rest

def baireOneModulusFromEventFlow (ef : EventFlow) : Option BaireOneModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireOneModulusUp.mk
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 0 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 1 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 2 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 3 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 4 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 5 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 6 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 7 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 8 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 9 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 10 ef))
      (baireOneModulusDecodeBHist (baireOneModulusEventAtDefault 11 ef)))

private theorem BaireOneModulusTasteGate_single_carrier_alignment_round_trip
    (x : BaireOneModulusUp) :
    baireOneModulusFromEventFlow (baireOneModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A T O W M R E H C P N =>
      change
        some
          (BaireOneModulusUp.mk
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist S))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist A))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist T))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist O))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist W))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist M))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist R))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist E))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist H))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist C))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist P))
            (baireOneModulusDecodeBHist (baireOneModulusEncodeBHist N))) =
          some (BaireOneModulusUp.mk S A T O W M R E H C P N)
      rw [BaireOneModulusTasteGate_single_carrier_alignment_decode_encode S,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode A,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode T,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode O,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode W,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode M,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode R,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode E,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode H,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode C,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode P,
        BaireOneModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireOneModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireOneModulusUp} :
    baireOneModulusToEventFlow x = baireOneModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireOneModulusFromEventFlow (baireOneModulusToEventFlow x) =
        baireOneModulusFromEventFlow (baireOneModulusToEventFlow y) :=
    congrArg baireOneModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireOneModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireOneModulusTasteGate_single_carrier_alignment_round_trip y)))

instance baireOneModulusBHistCarrier : BHistCarrier BaireOneModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireOneModulusToEventFlow
  fromEventFlow := baireOneModulusFromEventFlow

instance baireOneModulusChapterTasteGate : ChapterTasteGate BaireOneModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireOneModulusFromEventFlow (baireOneModulusToEventFlow x) = some x
    exact BaireOneModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireOneModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BaireOneModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, baireOneModulusDecodeBHist (baireOneModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BaireOneModulusUp) ∧
        Nonempty (ChapterTasteGate BaireOneModulusUp) ∧
          baireOneModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BaireOneModulusTasteGate_single_carrier_alignment_decode_encode,
      ⟨baireOneModulusBHistCarrier⟩,
      ⟨baireOneModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BaireOneModulusUp
