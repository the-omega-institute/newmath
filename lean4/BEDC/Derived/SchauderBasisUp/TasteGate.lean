import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchauderBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchauderBasisUp : Type where
  | mk (V Nrm B C S E R H T P L : BHist) : SchauderBasisUp
  deriving DecidableEq

def schauderBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schauderBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schauderBasisEncodeBHist h

def schauderBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schauderBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schauderBasisDecodeBHist tail)

private theorem SchauderBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, schauderBasisDecodeBHist (schauderBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schauderBasisFields : SchauderBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchauderBasisUp.mk V Nrm B C S E R H T P L => [V, Nrm, B, C, S, E, R, H, T, P, L]

def schauderBasisToEventFlow : SchauderBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (schauderBasisFields x).map schauderBasisEncodeBHist

private def schauderBasisEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schauderBasisEventAt index rest

def schauderBasisFromEventFlow (ef : EventFlow) : Option SchauderBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SchauderBasisUp.mk
      (schauderBasisDecodeBHist (schauderBasisEventAt 0 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 1 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 2 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 3 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 4 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 5 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 6 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 7 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 8 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 9 ef))
      (schauderBasisDecodeBHist (schauderBasisEventAt 10 ef)))

private theorem SchauderBasisTasteGate_single_carrier_alignment_round_trip
    (x : SchauderBasisUp) :
    schauderBasisFromEventFlow (schauderBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk V Nrm B C S E R H T P L =>
      change
        some
          (SchauderBasisUp.mk
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist V))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist Nrm))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist B))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist C))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist S))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist E))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist R))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist H))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist T))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist P))
            (schauderBasisDecodeBHist (schauderBasisEncodeBHist L))) =
          some (SchauderBasisUp.mk V Nrm B C S E R H T P L)
      rw [SchauderBasisTasteGate_single_carrier_alignment_decode_encode V,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode Nrm,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode B,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode C,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode S,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode E,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode R,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode H,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode T,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode P,
        SchauderBasisTasteGate_single_carrier_alignment_decode_encode L]

private theorem SchauderBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchauderBasisUp} :
    schauderBasisToEventFlow x = schauderBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schauderBasisFromEventFlow (schauderBasisToEventFlow x) =
        schauderBasisFromEventFlow (schauderBasisToEventFlow y) :=
    congrArg schauderBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SchauderBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SchauderBasisTasteGate_single_carrier_alignment_round_trip y)))

instance schauderBasisBHistCarrier : BHistCarrier SchauderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schauderBasisToEventFlow
  fromEventFlow := schauderBasisFromEventFlow

instance schauderBasisChapterTasteGate : ChapterTasteGate SchauderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schauderBasisFromEventFlow (schauderBasisToEventFlow x) = some x
    exact SchauderBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchauderBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SchauderBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, schauderBasisDecodeBHist (schauderBasisEncodeBHist h) = h) ∧
      (∀ x : SchauderBasisUp,
        schauderBasisFromEventFlow (schauderBasisToEventFlow x) = some x) ∧
      (∀ x y : SchauderBasisUp,
        schauderBasisToEventFlow x = schauderBasisToEventFlow y → x = y) ∧
      schauderBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SchauderBasisTasteGate_single_carrier_alignment_decode_encode,
      SchauderBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SchauderBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SchauderBasisUp
