import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArtinianRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArtinianRingUp : Type where
  | mk (R C I D L H Q P N : BHist) : ArtinianRingUp
  deriving DecidableEq

def artinianRingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: artinianRingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: artinianRingEncodeBHist h

def artinianRingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (artinianRingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (artinianRingDecodeBHist tail)

private theorem ArtinianRingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, artinianRingDecodeBHist (artinianRingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def artinianRingFields : ArtinianRingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArtinianRingUp.mk R C I D L H Q P N => [R, C, I, D, L, H, Q, P, N]

def artinianRingToEventFlow : ArtinianRingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (artinianRingFields x).map artinianRingEncodeBHist

private def artinianRingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => artinianRingEventAtDefault index rest

def artinianRingFromEventFlow (ef : EventFlow) : Option ArtinianRingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArtinianRingUp.mk
      (artinianRingDecodeBHist (artinianRingEventAtDefault 0 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 1 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 2 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 3 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 4 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 5 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 6 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 7 ef))
      (artinianRingDecodeBHist (artinianRingEventAtDefault 8 ef)))

private theorem ArtinianRingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArtinianRingUp, artinianRingFromEventFlow (artinianRingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R C I D L H Q P N =>
      change
        some
          (ArtinianRingUp.mk
            (artinianRingDecodeBHist (artinianRingEncodeBHist R))
            (artinianRingDecodeBHist (artinianRingEncodeBHist C))
            (artinianRingDecodeBHist (artinianRingEncodeBHist I))
            (artinianRingDecodeBHist (artinianRingEncodeBHist D))
            (artinianRingDecodeBHist (artinianRingEncodeBHist L))
            (artinianRingDecodeBHist (artinianRingEncodeBHist H))
            (artinianRingDecodeBHist (artinianRingEncodeBHist Q))
            (artinianRingDecodeBHist (artinianRingEncodeBHist P))
            (artinianRingDecodeBHist (artinianRingEncodeBHist N))) =
          some (ArtinianRingUp.mk R C I D L H Q P N)
      rw [ArtinianRingTasteGate_single_carrier_alignment_decode R,
        ArtinianRingTasteGate_single_carrier_alignment_decode C,
        ArtinianRingTasteGate_single_carrier_alignment_decode I,
        ArtinianRingTasteGate_single_carrier_alignment_decode D,
        ArtinianRingTasteGate_single_carrier_alignment_decode L,
        ArtinianRingTasteGate_single_carrier_alignment_decode H,
        ArtinianRingTasteGate_single_carrier_alignment_decode Q,
        ArtinianRingTasteGate_single_carrier_alignment_decode P,
        ArtinianRingTasteGate_single_carrier_alignment_decode N]

private theorem ArtinianRingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArtinianRingUp} :
    artinianRingToEventFlow x = artinianRingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      artinianRingFromEventFlow (artinianRingToEventFlow x) =
        artinianRingFromEventFlow (artinianRingToEventFlow y) :=
    congrArg artinianRingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArtinianRingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ArtinianRingTasteGate_single_carrier_alignment_round_trip y)))

instance artinianRingBHistCarrier : BHistCarrier ArtinianRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := artinianRingToEventFlow
  fromEventFlow := artinianRingFromEventFlow

instance artinianRingChapterTasteGate : ChapterTasteGate ArtinianRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change artinianRingFromEventFlow (artinianRingToEventFlow x) = some x
    exact ArtinianRingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArtinianRingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ArtinianRingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  artinianRingChapterTasteGate

theorem ArtinianRingTasteGate_single_carrier_alignment :
    (∀ h : BHist, artinianRingDecodeBHist (artinianRingEncodeBHist h) = h) ∧
      (∀ x : ArtinianRingUp,
        artinianRingFromEventFlow (artinianRingToEventFlow x) = some x) ∧
        (∀ x y : ArtinianRingUp,
          artinianRingToEventFlow x = artinianRingToEventFlow y → x = y) ∧
          artinianRingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ArtinianRingTasteGate_single_carrier_alignment_decode,
      ArtinianRingTasteGate_single_carrier_alignment_round_trip,
      fun x y hxy => ArtinianRingTasteGate_single_carrier_alignment_toEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.ArtinianRingUp
