import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SamuelCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SamuelCompactificationUp : Type where
  | mk (U B D K W R H C P N : BHist) : SamuelCompactificationUp
  deriving DecidableEq

def samuelCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: samuelCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: samuelCompactificationEncodeBHist h

def samuelCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (samuelCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (samuelCompactificationDecodeBHist tail)

private theorem SamuelCompactificationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, samuelCompactificationDecodeBHist
      (samuelCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def samuelCompactificationFields : SamuelCompactificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SamuelCompactificationUp.mk U B D K W R H C P N => [U, B, D, K, W, R, H, C, P, N]

def samuelCompactificationToEventFlow : SamuelCompactificationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map samuelCompactificationEncodeBHist (samuelCompactificationFields x)

private def samuelCompactificationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => samuelCompactificationEventAt index rest

def samuelCompactificationFromEventFlow : EventFlow → Option SamuelCompactificationUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SamuelCompactificationUp.mk
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 0 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 1 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 2 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 3 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 4 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 5 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 6 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 7 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 8 ef))
          (samuelCompactificationDecodeBHist (samuelCompactificationEventAt 9 ef)))

private theorem SamuelCompactificationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SamuelCompactificationUp,
      samuelCompactificationFromEventFlow (samuelCompactificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U B D K W R H C P N =>
      change
        some
          (SamuelCompactificationUp.mk
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist U))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist B))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist D))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist K))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist W))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist R))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist H))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist C))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist P))
            (samuelCompactificationDecodeBHist (samuelCompactificationEncodeBHist N))) =
          some (SamuelCompactificationUp.mk U B D K W R H C P N)
      rw [SamuelCompactificationTasteGate_single_carrier_alignment_decode U,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode B,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode D,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode K,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode W,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode R,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode H,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode C,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode P,
        SamuelCompactificationTasteGate_single_carrier_alignment_decode N]

private theorem SamuelCompactificationTasteGate_single_carrier_alignment_injective
    {x y : SamuelCompactificationUp} :
    samuelCompactificationToEventFlow x = samuelCompactificationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      samuelCompactificationFromEventFlow (samuelCompactificationToEventFlow x) =
        samuelCompactificationFromEventFlow (samuelCompactificationToEventFlow y) :=
    congrArg samuelCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SamuelCompactificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SamuelCompactificationTasteGate_single_carrier_alignment_round_trip y)))

instance samuelCompactificationBHistCarrier : BHistCarrier SamuelCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := samuelCompactificationToEventFlow
  fromEventFlow := samuelCompactificationFromEventFlow

instance samuelCompactificationChapterTasteGate : ChapterTasteGate SamuelCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change samuelCompactificationFromEventFlow (samuelCompactificationToEventFlow x) = some x
    exact SamuelCompactificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SamuelCompactificationTasteGate_single_carrier_alignment_injective heq)

private theorem SamuelCompactificationTasteGate_single_carrier_alignment_instances :
    Nonempty (BHistCarrier SamuelCompactificationUp) ∧
      Nonempty (ChapterTasteGate SamuelCompactificationUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨samuelCompactificationBHistCarrier⟩, ⟨samuelCompactificationChapterTasteGate⟩⟩

theorem SamuelCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist, samuelCompactificationDecodeBHist
      (samuelCompactificationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SamuelCompactificationUp) ∧
        Nonempty (ChapterTasteGate SamuelCompactificationUp) ∧
          samuelCompactificationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact SamuelCompactificationTasteGate_single_carrier_alignment_decode
  · constructor
    · exact SamuelCompactificationTasteGate_single_carrier_alignment_instances.left
    · constructor
      · exact SamuelCompactificationTasteGate_single_carrier_alignment_instances.right
      · rfl

end BEDC.Derived.SamuelCompactificationUp
