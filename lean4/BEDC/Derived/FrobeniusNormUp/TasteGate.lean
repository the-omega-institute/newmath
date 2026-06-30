import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrobeniusNormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrobeniusNormUp : Type where
  | mk (A E S R N0 V G O H C P L : BHist) : FrobeniusNormUp
  deriving DecidableEq

def frobeniusNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frobeniusNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frobeniusNormEncodeBHist h

def frobeniusNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frobeniusNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frobeniusNormDecodeBHist tail)

private theorem FrobeniusNormTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frobeniusNormDecodeBHist (frobeniusNormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frobeniusNormFields : FrobeniusNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrobeniusNormUp.mk A E S R N0 V G O H C P L => [A, E, S, R, N0, V, G, O, H, C, P, L]

def frobeniusNormToEventFlow : FrobeniusNormUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (frobeniusNormFields x).map frobeniusNormEncodeBHist

private def frobeniusNormEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frobeniusNormEventAtDefault index rest

def frobeniusNormFromEventFlow (ef : EventFlow) : Option FrobeniusNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrobeniusNormUp.mk
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 0 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 1 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 2 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 3 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 4 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 5 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 6 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 7 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 8 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 9 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 10 ef))
      (frobeniusNormDecodeBHist (frobeniusNormEventAtDefault 11 ef)))

private theorem FrobeniusNormTasteGate_single_carrier_alignment_round_trip
    (x : FrobeniusNormUp) :
    frobeniusNormFromEventFlow (frobeniusNormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A E S R N0 V G O H C P L =>
      change
        some
          (FrobeniusNormUp.mk
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist A))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist E))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist S))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist R))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist N0))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist V))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist G))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist O))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist H))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist C))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist P))
            (frobeniusNormDecodeBHist (frobeniusNormEncodeBHist L))) =
          some (FrobeniusNormUp.mk A E S R N0 V G O H C P L)
      rw [FrobeniusNormTasteGate_single_carrier_alignment_decode A,
        FrobeniusNormTasteGate_single_carrier_alignment_decode E,
        FrobeniusNormTasteGate_single_carrier_alignment_decode S,
        FrobeniusNormTasteGate_single_carrier_alignment_decode R,
        FrobeniusNormTasteGate_single_carrier_alignment_decode N0,
        FrobeniusNormTasteGate_single_carrier_alignment_decode V,
        FrobeniusNormTasteGate_single_carrier_alignment_decode G,
        FrobeniusNormTasteGate_single_carrier_alignment_decode O,
        FrobeniusNormTasteGate_single_carrier_alignment_decode H,
        FrobeniusNormTasteGate_single_carrier_alignment_decode C,
        FrobeniusNormTasteGate_single_carrier_alignment_decode P,
        FrobeniusNormTasteGate_single_carrier_alignment_decode L]

private theorem FrobeniusNormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrobeniusNormUp} :
    frobeniusNormToEventFlow x = frobeniusNormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frobeniusNormFromEventFlow (frobeniusNormToEventFlow x) =
        frobeniusNormFromEventFlow (frobeniusNormToEventFlow y) :=
    congrArg frobeniusNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrobeniusNormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FrobeniusNormTasteGate_single_carrier_alignment_round_trip y)))

instance frobeniusNormBHistCarrier : BHistCarrier FrobeniusNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frobeniusNormToEventFlow
  fromEventFlow := frobeniusNormFromEventFlow

instance frobeniusNormChapterTasteGate : ChapterTasteGate FrobeniusNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frobeniusNormFromEventFlow (frobeniusNormToEventFlow x) = some x
    exact FrobeniusNormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrobeniusNormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FrobeniusNormTasteGate_single_carrier_alignment :
    (∀ h : BHist, frobeniusNormDecodeBHist (frobeniusNormEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FrobeniusNormUp) ∧ Nonempty (ChapterTasteGate FrobeniusNormUp) ∧
        frobeniusNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FrobeniusNormTasteGate_single_carrier_alignment_decode,
      ⟨frobeniusNormBHistCarrier⟩, ⟨frobeniusNormChapterTasteGate⟩, rfl⟩

end BEDC.Derived.FrobeniusNormUp
