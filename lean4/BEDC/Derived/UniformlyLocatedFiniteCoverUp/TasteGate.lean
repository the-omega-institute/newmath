import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformlyLocatedFiniteCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformlyLocatedFiniteCoverUp : Type where
  | mk (I F L M H C P N : BHist) : UniformlyLocatedFiniteCoverUp
  deriving DecidableEq

def uniformlyLocatedFiniteCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformlyLocatedFiniteCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformlyLocatedFiniteCoverEncodeBHist h

def uniformlyLocatedFiniteCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformlyLocatedFiniteCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformlyLocatedFiniteCoverDecodeBHist tail)

private theorem UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformlyLocatedFiniteCoverToEventFlow : UniformlyLocatedFiniteCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformlyLocatedFiniteCoverUp.mk I F L M H C P N =>
      [uniformlyLocatedFiniteCoverEncodeBHist I,
        uniformlyLocatedFiniteCoverEncodeBHist F,
        uniformlyLocatedFiniteCoverEncodeBHist L,
        uniformlyLocatedFiniteCoverEncodeBHist M,
        uniformlyLocatedFiniteCoverEncodeBHist H,
        uniformlyLocatedFiniteCoverEncodeBHist C,
        uniformlyLocatedFiniteCoverEncodeBHist P,
        uniformlyLocatedFiniteCoverEncodeBHist N]

private def uniformlyLocatedFiniteCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformlyLocatedFiniteCoverEventAtDefault index rest

def uniformlyLocatedFiniteCoverFromEventFlow
    (ef : EventFlow) : Option UniformlyLocatedFiniteCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformlyLocatedFiniteCoverUp.mk
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 0 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 1 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 2 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 3 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 4 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 5 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 6 ef))
      (uniformlyLocatedFiniteCoverDecodeBHist
        (uniformlyLocatedFiniteCoverEventAtDefault 7 ef)))

private theorem UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformlyLocatedFiniteCoverUp,
      uniformlyLocatedFiniteCoverFromEventFlow
        (uniformlyLocatedFiniteCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F L M H C P N =>
      change
        some
          (UniformlyLocatedFiniteCoverUp.mk
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist I))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist F))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist L))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist M))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist H))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist C))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist P))
            (uniformlyLocatedFiniteCoverDecodeBHist
              (uniformlyLocatedFiniteCoverEncodeBHist N))) =
          some (UniformlyLocatedFiniteCoverUp.mk I F L M H C P N)
      rw [UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode I,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode F,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode L,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode M,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode H,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode C,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode P,
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode N]

private theorem UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_injective
    {x y : UniformlyLocatedFiniteCoverUp} :
    uniformlyLocatedFiniteCoverToEventFlow x =
        uniformlyLocatedFiniteCoverToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformlyLocatedFiniteCoverFromEventFlow
          (uniformlyLocatedFiniteCoverToEventFlow x) =
        uniformlyLocatedFiniteCoverFromEventFlow
          (uniformlyLocatedFiniteCoverToEventFlow y) :=
    congrArg uniformlyLocatedFiniteCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_round_trip y)))

instance uniformlyLocatedFiniteCoverBHistCarrier :
    BHistCarrier UniformlyLocatedFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformlyLocatedFiniteCoverToEventFlow
  fromEventFlow := uniformlyLocatedFiniteCoverFromEventFlow

instance uniformlyLocatedFiniteCoverChapterTasteGate :
    ChapterTasteGate UniformlyLocatedFiniteCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformlyLocatedFiniteCoverFromEventFlow
      (uniformlyLocatedFiniteCoverToEventFlow x) = some x
    exact UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_injective heq)

theorem UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformlyLocatedFiniteCoverDecodeBHist
      (uniformlyLocatedFiniteCoverEncodeBHist h) = h) ∧
      (∀ x : UniformlyLocatedFiniteCoverUp,
        uniformlyLocatedFiniteCoverFromEventFlow
          (uniformlyLocatedFiniteCoverToEventFlow x) = some x) ∧
        (∀ x y : UniformlyLocatedFiniteCoverUp,
          uniformlyLocatedFiniteCoverToEventFlow x =
              uniformlyLocatedFiniteCoverToEventFlow y →
            x = y) ∧
          uniformlyLocatedFiniteCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_decode,
      UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformlyLocatedFiniteCoverTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.UniformlyLocatedFiniteCoverUp
