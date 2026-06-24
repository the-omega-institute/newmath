import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinkowskiFunctionalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinkowskiFunctionalUp : Type where
  | mk (X V A B L R H C P N : BHist) : MinkowskiFunctionalUp
  deriving DecidableEq

def minkowskiFunctionalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minkowskiFunctionalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minkowskiFunctionalEncodeBHist h

def minkowskiFunctionalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minkowskiFunctionalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minkowskiFunctionalDecodeBHist tail)

private theorem MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem MinkowskiFunctionalTasteGate_single_carrier_alignment_encode_decode :
    ∀ raw : List BMark,
      minkowskiFunctionalEncodeBHist (minkowskiFunctionalDecodeBHist raw) = raw := by
  -- BEDC touchpoint anchor: BHist BMark
  intro raw
  induction raw with
  | nil => rfl
  | cons mark tail ih =>
      cases mark with
      | b0 => exact congrArg (List.cons BMark.b0) ih
      | b1 => exact congrArg (List.cons BMark.b1) ih

def minkowskiFunctionalFields : MinkowskiFunctionalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinkowskiFunctionalUp.mk X V A B L R H C P N => [X, V, A, B, L, R, H, C, P, N]

def minkowskiFunctionalToEventFlow : MinkowskiFunctionalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (minkowskiFunctionalFields x).map minkowskiFunctionalEncodeBHist

private def minkowskiFunctionalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => minkowskiFunctionalEventAtDefault index rest

def minkowskiFunctionalFromEventFlow (ef : EventFlow) : Option MinkowskiFunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MinkowskiFunctionalUp.mk
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 0 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 1 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 2 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 3 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 4 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 5 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 6 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 7 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 8 ef))
      (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEventAtDefault 9 ef)))

private theorem MinkowskiFunctionalTasteGate_single_carrier_alignment_round_trip
    (x : MinkowskiFunctionalUp) :
    minkowskiFunctionalFromEventFlow (minkowskiFunctionalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X V A B L R H C P N =>
      change
        some
          (MinkowskiFunctionalUp.mk
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist X))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist V))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist A))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist B))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist L))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist R))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist H))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist C))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist P))
            (minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist N))) =
          some (MinkowskiFunctionalUp.mk X V A B L R H C P N)
      rw [MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode X,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode V,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode A,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode B,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode L,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode R,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode H,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode C,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode P,
        MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode N]

private theorem MinkowskiFunctionalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MinkowskiFunctionalUp} :
    minkowskiFunctionalToEventFlow x = minkowskiFunctionalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minkowskiFunctionalFromEventFlow (minkowskiFunctionalToEventFlow x) =
        minkowskiFunctionalFromEventFlow (minkowskiFunctionalToEventFlow y) :=
    congrArg minkowskiFunctionalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MinkowskiFunctionalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MinkowskiFunctionalTasteGate_single_carrier_alignment_round_trip y)))

instance minkowskiFunctionalBHistCarrier : BHistCarrier MinkowskiFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minkowskiFunctionalToEventFlow
  fromEventFlow := minkowskiFunctionalFromEventFlow

instance minkowskiFunctionalChapterTasteGate : ChapterTasteGate MinkowskiFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change minkowskiFunctionalFromEventFlow (minkowskiFunctionalToEventFlow x) = some x
    exact MinkowskiFunctionalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MinkowskiFunctionalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MinkowskiFunctionalTasteGate_single_carrier_alignment :
    (∀ h : BHist, minkowskiFunctionalDecodeBHist (minkowskiFunctionalEncodeBHist h) = h) ∧
      (∀ raw : List BMark,
        minkowskiFunctionalEncodeBHist (minkowskiFunctionalDecodeBHist raw) = raw) ∧
        Nonempty (BHistCarrier MinkowskiFunctionalUp) ∧
          Nonempty (ChapterTasteGate MinkowskiFunctionalUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MinkowskiFunctionalTasteGate_single_carrier_alignment_decode_encode,
      MinkowskiFunctionalTasteGate_single_carrier_alignment_encode_decode,
      ⟨minkowskiFunctionalBHistCarrier⟩,
      ⟨minkowskiFunctionalChapterTasteGate⟩⟩

end BEDC.Derived.MinkowskiFunctionalUp
