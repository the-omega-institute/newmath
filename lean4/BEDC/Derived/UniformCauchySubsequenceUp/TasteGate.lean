import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchySubsequenceUp : Type where
  | mk (B T U W D Q R E H C P N : BHist) : UniformCauchySubsequenceUp
  deriving DecidableEq

def uniformCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchySubsequenceEncodeBHist h

def uniformCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchySubsequenceDecodeBHist tail)

private theorem UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchySubsequenceFields : UniformCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchySubsequenceUp.mk B T U W D Q R E H C P N => [B, T, U, W, D, Q, R, E, H, C, P, N]

def uniformCauchySubsequenceToEventFlow : UniformCauchySubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformCauchySubsequenceFields x).map uniformCauchySubsequenceEncodeBHist

private def uniformCauchySubsequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCauchySubsequenceEventAtDefault index rest

def uniformCauchySubsequenceFromEventFlow (ef : EventFlow) :
    Option UniformCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchySubsequenceUp.mk
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 0 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 1 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 2 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 3 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 4 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 5 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 6 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 7 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 8 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 9 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 10 ef))
      (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEventAtDefault 11 ef)))

private theorem UniformCauchySubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCauchySubsequenceUp,
      uniformCauchySubsequenceFromEventFlow (uniformCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B T U W D Q R E H C P N =>
      change
        some
          (UniformCauchySubsequenceUp.mk
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist B))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist T))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist U))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist W))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist D))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist Q))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist R))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist E))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist H))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist C))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist P))
            (uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist N))) =
          some (UniformCauchySubsequenceUp.mk B T U W D Q R E H C P N)
      rw [UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode B,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode T,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode U,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode W,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode D,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode Q,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode R,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode E,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode H,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode C,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode P,
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchySubsequenceUp} :
    uniformCauchySubsequenceToEventFlow x = uniformCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchySubsequenceFromEventFlow (uniformCauchySubsequenceToEventFlow x) =
        uniformCauchySubsequenceFromEventFlow (uniformCauchySubsequenceToEventFlow y) :=
    congrArg uniformCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCauchySubsequenceTasteGate_single_carrier_alignment_round_trip y)))

instance uniformCauchySubsequenceBHistCarrier : BHistCarrier UniformCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchySubsequenceToEventFlow
  fromEventFlow := uniformCauchySubsequenceFromEventFlow

instance uniformCauchySubsequenceChapterTasteGate :
    ChapterTasteGate UniformCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCauchySubsequenceFromEventFlow (uniformCauchySubsequenceToEventFlow x) =
      some x
    exact UniformCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchySubsequenceChapterTasteGate

theorem UniformCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformCauchySubsequenceDecodeBHist (uniformCauchySubsequenceEncodeBHist h) = h) ∧
      (∀ x : UniformCauchySubsequenceUp,
        uniformCauchySubsequenceFromEventFlow (uniformCauchySubsequenceToEventFlow x) =
          some x) ∧
        (∀ x y : UniformCauchySubsequenceUp,
          uniformCauchySubsequenceToEventFlow x = uniformCauchySubsequenceToEventFlow y →
            x = y) ∧
          uniformCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode,
      UniformCauchySubsequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformCauchySubsequenceUp
