import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceUp : Type where
  | mk (source window readback real schedule transport replay provenance name : BHist) :
      UniformConvergenceUp
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

private theorem uniformConvergence_decode_encode_bhist :
    ∀ h : BHist,
      uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformConvergenceFields : UniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceUp.mk source window readback real schedule transport replay provenance
      name =>
      [source, window, readback, real, schedule, transport, replay, provenance, name]

def uniformConvergenceToEventFlow : UniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformConvergenceFields x).map uniformConvergenceEncodeBHist

private def uniformConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformConvergenceEventAt index rest

def uniformConvergenceFromEventFlow
    (flow : EventFlow) : Option UniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformConvergenceUp.mk
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 0 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 1 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 2 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 3 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 4 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 5 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 6 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 7 flow))
      (uniformConvergenceDecodeBHist (uniformConvergenceEventAt 8 flow)))

private theorem uniformConvergence_round_trip :
    ∀ x : UniformConvergenceUp,
      uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source window readback real schedule transport replay provenance name =>
      change
        some
          (UniformConvergenceUp.mk
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist source))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist window))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist readback))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist real))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist schedule))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist transport))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist replay))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist provenance))
            (uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist name))) =
          some
            (UniformConvergenceUp.mk source window readback real schedule transport replay
              provenance name)
      rw [uniformConvergence_decode_encode_bhist source,
        uniformConvergence_decode_encode_bhist window,
        uniformConvergence_decode_encode_bhist readback,
        uniformConvergence_decode_encode_bhist real,
        uniformConvergence_decode_encode_bhist schedule,
        uniformConvergence_decode_encode_bhist transport,
        uniformConvergence_decode_encode_bhist replay,
        uniformConvergence_decode_encode_bhist provenance,
        uniformConvergence_decode_encode_bhist name]

private theorem uniformConvergenceToEventFlow_injective
    {x y : UniformConvergenceUp} :
    uniformConvergenceToEventFlow x = uniformConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) =
        uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow y) :=
    congrArg uniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformConvergence_round_trip x).symm
      (Eq.trans hread (uniformConvergence_round_trip y)))

instance uniformConvergenceBHistCarrier :
    BHistCarrier UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceToEventFlow
  fromEventFlow := uniformConvergenceFromEventFlow

instance uniformConvergenceChapterTasteGate :
    ChapterTasteGate UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x
    exact uniformConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformConvergenceChapterTasteGate

theorem UniformConvergenceTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier UniformConvergenceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate UniformConvergenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨uniformConvergenceBHistCarrier⟩
  · exact ⟨uniformConvergenceChapterTasteGate⟩

end BEDC.Derived.UniformConvergenceUp
