import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchySubnetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchySubnetUp : Type where
  | mk (S M W D R E L H C P N : BHist) : UniformCauchySubnetUp
  deriving DecidableEq

def uniformCauchySubnetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchySubnetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchySubnetEncodeBHist h

private def uniformCauchySubnetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchySubnetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchySubnetDecodeBHist tail)

private theorem UniformCauchySubnetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformCauchySubnetToEventFlow : UniformCauchySubnetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchySubnetUp.mk S M W D R E L H C P N =>
      [uniformCauchySubnetEncodeBHist S,
        uniformCauchySubnetEncodeBHist M,
        uniformCauchySubnetEncodeBHist W,
        uniformCauchySubnetEncodeBHist D,
        uniformCauchySubnetEncodeBHist R,
        uniformCauchySubnetEncodeBHist E,
        uniformCauchySubnetEncodeBHist L,
        uniformCauchySubnetEncodeBHist H,
        uniformCauchySubnetEncodeBHist C,
        uniformCauchySubnetEncodeBHist P,
        uniformCauchySubnetEncodeBHist N]

private def uniformCauchySubnetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCauchySubnetEventAtDefault index rest

private def uniformCauchySubnetFromEventFlow
    (ef : EventFlow) : Option UniformCauchySubnetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchySubnetUp.mk
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 0 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 1 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 2 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 3 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 4 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 5 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 6 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 7 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 8 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 9 ef))
      (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEventAtDefault 10 ef)))

private theorem UniformCauchySubnetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCauchySubnetUp,
      uniformCauchySubnetFromEventFlow (uniformCauchySubnetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W D R E L H C P N =>
      change
        some
          (UniformCauchySubnetUp.mk
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist S))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist M))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist W))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist D))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist R))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist E))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist L))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist H))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist C))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist P))
            (uniformCauchySubnetDecodeBHist (uniformCauchySubnetEncodeBHist N))) =
          some (UniformCauchySubnetUp.mk S M W D R E L H C P N)
      rw [UniformCauchySubnetTasteGate_single_carrier_alignment_decode S,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode M,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode W,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode D,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode R,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode E,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode L,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode H,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode C,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode P,
        UniformCauchySubnetTasteGate_single_carrier_alignment_decode N]

private theorem UniformCauchySubnetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchySubnetUp} :
    uniformCauchySubnetToEventFlow x = uniformCauchySubnetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchySubnetFromEventFlow (uniformCauchySubnetToEventFlow x) =
        uniformCauchySubnetFromEventFlow (uniformCauchySubnetToEventFlow y) :=
    congrArg uniformCauchySubnetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCauchySubnetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformCauchySubnetTasteGate_single_carrier_alignment_round_trip y)))

instance uniformCauchySubnetBHistCarrier : BHistCarrier UniformCauchySubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchySubnetToEventFlow
  fromEventFlow := uniformCauchySubnetFromEventFlow

instance uniformCauchySubnetChapterTasteGate : ChapterTasteGate UniformCauchySubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact UniformCauchySubnetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformCauchySubnetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformCauchySubnetTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier UniformCauchySubnetUp) ∧
      Nonempty (ChapterTasteGate UniformCauchySubnetUp) ∧
        uniformCauchySubnetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨uniformCauchySubnetBHistCarrier⟩
  · constructor
    · exact ⟨uniformCauchySubnetChapterTasteGate⟩
    · rfl

end BEDC.Derived.UniformCauchySubnetUp.TasteGate
