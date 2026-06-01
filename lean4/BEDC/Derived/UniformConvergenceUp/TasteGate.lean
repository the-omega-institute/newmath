import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceUp : Type where
  | mk (F W Q R T H C P N : BHist) : UniformConvergenceUp
  deriving DecidableEq

def uniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformConvergenceEncodeBHist h

def uniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformConvergenceDecodeBHist tail)

private theorem UniformConvergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformConvergenceFields : UniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceUp.mk F W Q R T H C P N => [F, W, Q, R, T, H, C, P, N]

def uniformConvergenceToEventFlow : UniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformConvergenceFields x).map uniformConvergenceEncodeBHist

private def uniformConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformConvergenceEventAtDefault index rest

def uniformConvergenceFromEventFlow : EventFlow → Option UniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (UniformConvergenceUp.mk
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 0 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 1 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 2 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 3 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 4 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 5 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 6 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 7 ef))
        (uniformConvergenceDecodeBHist (uniformConvergenceEventAtDefault 8 ef)))

private theorem UniformConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformConvergenceUp,
      uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W Q R T H C P N =>
      change
        some
          (UniformConvergenceUp.mk
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist F))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist W))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist Q))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist R))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist T))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist H))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist C))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist P))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist N))) =
          some (UniformConvergenceUp.mk F W Q R T H C P N)
      rw [UniformConvergenceTasteGate_single_carrier_alignment_decode F,
        UniformConvergenceTasteGate_single_carrier_alignment_decode W,
        UniformConvergenceTasteGate_single_carrier_alignment_decode Q,
        UniformConvergenceTasteGate_single_carrier_alignment_decode R,
        UniformConvergenceTasteGate_single_carrier_alignment_decode T,
        UniformConvergenceTasteGate_single_carrier_alignment_decode H,
        UniformConvergenceTasteGate_single_carrier_alignment_decode C,
        UniformConvergenceTasteGate_single_carrier_alignment_decode P,
        UniformConvergenceTasteGate_single_carrier_alignment_decode N]

private theorem UniformConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformConvergenceUp} :
    uniformConvergenceToEventFlow x = uniformConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) =
        uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow y) :=
    congrArg uniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformConvergenceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : UniformConvergenceUp,
      uniformConvergenceFields x = uniformConvergenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F W Q R T H C P N =>
      cases y with
      | mk F' W' Q' R' T' H' C' P' N' =>
          cases hfields
          rfl

instance uniformConvergenceBHistCarrier : BHistCarrier UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceToEventFlow
  fromEventFlow := uniformConvergenceFromEventFlow

instance uniformConvergenceChapterTasteGate :
    ChapterTasteGate UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x
    exact UniformConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformConvergenceFieldFaithful : FieldFaithful UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformConvergenceFields
  field_faithful := UniformConvergenceTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate UniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformConvergenceChapterTasteGate

theorem UniformConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformConvergenceUp) ∧
        Nonempty (ChapterTasteGate UniformConvergenceUp) ∧
          uniformConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact UniformConvergenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨uniformConvergenceBHistCarrier⟩
    · constructor
      · exact ⟨uniformConvergenceChapterTasteGate⟩
      · rfl

end BEDC.Derived.UniformConvergenceUp
