import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformlyConvexSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformlyConvexSpaceUp : Type where
  | mk (N R A M Delta Q H T P C : BHist) : UniformlyConvexSpaceUp
  deriving DecidableEq

def uniformlyConvexSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformlyConvexSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformlyConvexSpaceEncodeBHist h

def uniformlyConvexSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformlyConvexSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformlyConvexSpaceDecodeBHist tail)

private theorem UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformlyConvexSpaceFields : UniformlyConvexSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformlyConvexSpaceUp.mk N R A M Delta Q H T P C =>
      [N, R, A, M, Delta, Q, H, T, P, C]

def uniformlyConvexSpaceToEventFlow : UniformlyConvexSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformlyConvexSpaceFields x).map uniformlyConvexSpaceEncodeBHist

private def uniformlyConvexSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformlyConvexSpaceEventAt index rest

def uniformlyConvexSpaceFromEventFlow (ef : EventFlow) : Option UniformlyConvexSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformlyConvexSpaceUp.mk
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 0 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 1 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 2 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 3 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 4 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 5 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 6 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 7 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 8 ef))
      (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEventAt 9 ef)))

private theorem UniformlyConvexSpaceTasteGate_single_carrier_alignment_round_trip
    (x : UniformlyConvexSpaceUp) :
    uniformlyConvexSpaceFromEventFlow (uniformlyConvexSpaceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk N R A M Delta Q H T P C =>
      change
        some
          (UniformlyConvexSpaceUp.mk
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist N))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist R))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist A))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist M))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist Delta))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist Q))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist H))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist T))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist P))
            (uniformlyConvexSpaceDecodeBHist (uniformlyConvexSpaceEncodeBHist C))) =
          some (UniformlyConvexSpaceUp.mk N R A M Delta Q H T P C)
      rw [UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode N,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode R,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode A,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode M,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode Delta,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode H,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode T,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode P,
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode C]

private theorem UniformlyConvexSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformlyConvexSpaceUp} :
    uniformlyConvexSpaceToEventFlow x = uniformlyConvexSpaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformlyConvexSpaceFromEventFlow (uniformlyConvexSpaceToEventFlow x) =
        uniformlyConvexSpaceFromEventFlow (uniformlyConvexSpaceToEventFlow y) :=
    congrArg uniformlyConvexSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformlyConvexSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformlyConvexSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance uniformlyConvexSpaceBHistCarrier : BHistCarrier UniformlyConvexSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformlyConvexSpaceToEventFlow
  fromEventFlow := uniformlyConvexSpaceFromEventFlow

instance uniformlyConvexSpaceChapterTasteGate : ChapterTasteGate UniformlyConvexSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformlyConvexSpaceFromEventFlow (uniformlyConvexSpaceToEventFlow x) = some x
    exact UniformlyConvexSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformlyConvexSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformlyConvexSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformlyConvexSpaceDecodeBHist
      (uniformlyConvexSpaceEncodeBHist h) = h) ∧
      (∀ x : UniformlyConvexSpaceUp,
        uniformlyConvexSpaceFromEventFlow
          (uniformlyConvexSpaceToEventFlow x) = some x) ∧
        (∀ x y : UniformlyConvexSpaceUp,
          uniformlyConvexSpaceToEventFlow x =
            uniformlyConvexSpaceToEventFlow y → x = y) ∧
          uniformlyConvexSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformlyConvexSpaceTasteGate_single_carrier_alignment_decode_encode,
      UniformlyConvexSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformlyConvexSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformlyConvexSpaceUp
