import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSupportRemovalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSupportRemovalUp : Type where
  | mk (K G D W T R L H C P N : BHist) : FiniteSupportRemovalUp
  deriving DecidableEq

def finiteSupportRemovalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSupportRemovalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSupportRemovalEncodeBHist h

def finiteSupportRemovalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSupportRemovalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSupportRemovalDecodeBHist tail)

private theorem FiniteSupportRemovalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSupportRemovalFields : FiniteSupportRemovalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSupportRemovalUp.mk K G D W T R L H C P N =>
      [K, G, D, W, T, R, L, H, C, P, N]

def finiteSupportRemovalToEventFlow : FiniteSupportRemovalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSupportRemovalFields x).map finiteSupportRemovalEncodeBHist

private def finiteSupportRemovalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSupportRemovalEventAtDefault index rest

def finiteSupportRemovalFromEventFlow (ef : EventFlow) :
    Option FiniteSupportRemovalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSupportRemovalUp.mk
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 0 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 1 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 2 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 3 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 4 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 5 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 6 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 7 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 8 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 9 ef))
      (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEventAtDefault 10 ef)))

private theorem FiniteSupportRemovalTasteGate_single_carrier_alignment_round_trip
    (x : FiniteSupportRemovalUp) :
    finiteSupportRemovalFromEventFlow (finiteSupportRemovalToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K G D W T R L H C P N =>
      change
        some
          (FiniteSupportRemovalUp.mk
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist K))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist G))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist D))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist W))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist T))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist R))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist L))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist H))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist C))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist P))
            (finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist N))) =
          some (FiniteSupportRemovalUp.mk K G D W T R L H C P N)
      rw [FiniteSupportRemovalTasteGate_single_carrier_alignment_decode K,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode G,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode D,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode W,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode T,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode R,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode L,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode H,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode C,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode P,
        FiniteSupportRemovalTasteGate_single_carrier_alignment_decode N]

private theorem FiniteSupportRemovalTasteGate_single_carrier_alignment_injective
    {x y : FiniteSupportRemovalUp} :
    finiteSupportRemovalToEventFlow x = finiteSupportRemovalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSupportRemovalFromEventFlow (finiteSupportRemovalToEventFlow x) =
        finiteSupportRemovalFromEventFlow (finiteSupportRemovalToEventFlow y) :=
    congrArg finiteSupportRemovalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSupportRemovalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSupportRemovalTasteGate_single_carrier_alignment_round_trip y)))

instance finiteSupportRemovalBHistCarrier :
    BHistCarrier FiniteSupportRemovalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSupportRemovalToEventFlow
  fromEventFlow := finiteSupportRemovalFromEventFlow

instance finiteSupportRemovalChapterTasteGate :
    ChapterTasteGate FiniteSupportRemovalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSupportRemovalFromEventFlow (finiteSupportRemovalToEventFlow x) = some x
    exact FiniteSupportRemovalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSupportRemovalTasteGate_single_carrier_alignment_injective heq)

theorem FiniteSupportRemovalTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier FiniteSupportRemovalUp,
      Nonempty (@ChapterTasteGate FiniteSupportRemovalUp carrier)) ∧
      (∀ h : BHist,
        finiteSupportRemovalDecodeBHist (finiteSupportRemovalEncodeBHist h) = h) ∧
      (∀ x : FiniteSupportRemovalUp,
        finiteSupportRemovalFromEventFlow (finiteSupportRemovalToEventFlow x) =
          some x) ∧
      finiteSupportRemovalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨finiteSupportRemovalBHistCarrier, ⟨finiteSupportRemovalChapterTasteGate⟩⟩,
      FiniteSupportRemovalTasteGate_single_carrier_alignment_decode,
      FiniteSupportRemovalTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.FiniteSupportRemovalUp
