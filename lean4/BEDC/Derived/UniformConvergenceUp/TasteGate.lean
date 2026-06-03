import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceUp.TasteGate

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
  | UniformConvergenceUp.mk F W Q R T H C P N => [F, W, Q, R, T, H, C, P, N]

def uniformConvergenceToEventFlow : UniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformConvergenceFields x).map uniformConvergenceEncodeBHist

private def uniformConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformConvergenceEventAt index rest

def uniformConvergenceFromEventFlow (flow : EventFlow) : Option UniformConvergenceUp :=
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
      rw [uniformConvergence_decode_encode_bhist F,
        uniformConvergence_decode_encode_bhist W,
        uniformConvergence_decode_encode_bhist Q,
        uniformConvergence_decode_encode_bhist R,
        uniformConvergence_decode_encode_bhist T,
        uniformConvergence_decode_encode_bhist H,
        uniformConvergence_decode_encode_bhist C,
        uniformConvergence_decode_encode_bhist P,
        uniformConvergence_decode_encode_bhist N]

private theorem uniformConvergenceToEventFlow_injective {x y : UniformConvergenceUp} :
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

instance uniformConvergenceBHistCarrier : BHistCarrier UniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceToEventFlow
  fromEventFlow := uniformConvergenceFromEventFlow

instance uniformConvergenceChapterTasteGate : ChapterTasteGate UniformConvergenceUp where
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
    Nonempty (BHistCarrier UniformConvergenceUp) ∧
      Nonempty (ChapterTasteGate UniformConvergenceUp) ∧
      (∀ h : BHist,
        uniformConvergenceDecodeBHist (uniformConvergenceEncodeBHist h) = h) ∧
      (∀ x : UniformConvergenceUp,
        uniformConvergenceFromEventFlow (uniformConvergenceToEventFlow x) = some x) ∧
      (∀ x y : UniformConvergenceUp,
        uniformConvergenceToEventFlow x = uniformConvergenceToEventFlow y → x = y) ∧
      uniformConvergenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨uniformConvergenceBHistCarrier⟩
  constructor
  · exact ⟨uniformConvergenceChapterTasteGate⟩
  constructor
  · exact uniformConvergence_decode_encode_bhist
  constructor
  · exact uniformConvergence_round_trip
  constructor
  · intro x y heq
    exact uniformConvergenceToEventFlow_injective heq
  · rfl

end BEDC.Derived.UniformConvergenceUp.TasteGate
