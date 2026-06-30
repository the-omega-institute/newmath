import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolishCauchyBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolishCauchyBasisUp : Type where
  | mk (X B K D S R O H C G N : BHist) : PolishCauchyBasisUp
  deriving DecidableEq

def polishCauchyBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: polishCauchyBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: polishCauchyBasisEncodeBHist h

def polishCauchyBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (polishCauchyBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (polishCauchyBasisDecodeBHist tail)

private theorem PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def polishCauchyBasisFields : PolishCauchyBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PolishCauchyBasisUp.mk X B K D S R O H C G N => [X, B, K, D, S, R, O, H, C, G, N]

def polishCauchyBasisToEventFlow : PolishCauchyBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (polishCauchyBasisFields x).map polishCauchyBasisEncodeBHist

private def polishCauchyBasisEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => polishCauchyBasisEventAt index rest

def polishCauchyBasisFromEventFlow (ef : EventFlow) : Option PolishCauchyBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PolishCauchyBasisUp.mk
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 0 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 1 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 2 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 3 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 4 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 5 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 6 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 7 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 8 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 9 ef))
      (polishCauchyBasisDecodeBHist (polishCauchyBasisEventAt 10 ef)))

private theorem PolishCauchyBasisTasteGate_single_carrier_alignment_round_trip
    (x : PolishCauchyBasisUp) :
    polishCauchyBasisFromEventFlow (polishCauchyBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X B K D S R O H C G N =>
      change
        some
          (PolishCauchyBasisUp.mk
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist X))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist B))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist K))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist D))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist S))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist R))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist O))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist H))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist C))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist G))
            (polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist N))) =
          some (PolishCauchyBasisUp.mk X B K D S R O H C G N)
      rw [PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode X,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode B,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode K,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode D,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode S,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode R,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode O,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode H,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode C,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode G,
        PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem PolishCauchyBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PolishCauchyBasisUp} :
    polishCauchyBasisToEventFlow x = polishCauchyBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      polishCauchyBasisFromEventFlow (polishCauchyBasisToEventFlow x) =
        polishCauchyBasisFromEventFlow (polishCauchyBasisToEventFlow y) :=
    congrArg polishCauchyBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PolishCauchyBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PolishCauchyBasisTasteGate_single_carrier_alignment_round_trip y)))

instance polishCauchyBasisBHistCarrier : BHistCarrier PolishCauchyBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := polishCauchyBasisToEventFlow
  fromEventFlow := polishCauchyBasisFromEventFlow

instance polishCauchyBasisChapterTasteGate : ChapterTasteGate PolishCauchyBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change polishCauchyBasisFromEventFlow (polishCauchyBasisToEventFlow x) = some x
    exact PolishCauchyBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PolishCauchyBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def PolishCauchyBasisTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate PolishCauchyBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  polishCauchyBasisChapterTasteGate

theorem PolishCauchyBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, polishCauchyBasisDecodeBHist (polishCauchyBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PolishCauchyBasisUp) ∧
        Nonempty (ChapterTasteGate PolishCauchyBasisUp) ∧
          polishCauchyBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PolishCauchyBasisTasteGate_single_carrier_alignment_decode_encode,
      ⟨polishCauchyBasisBHistCarrier⟩,
      ⟨polishCauchyBasisChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PolishCauchyBasisUp
