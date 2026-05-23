import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformBoundednessUp : Type where
  | mk (F W B N R S Q H C P L : BHist) : UniformBoundednessUp
  deriving DecidableEq

def uniformBoundednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformBoundednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformBoundednessEncodeBHist h

def uniformBoundednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformBoundednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformBoundednessDecodeBHist tail)

private theorem UniformBoundednessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformBoundednessFields : UniformBoundednessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformBoundednessUp.mk F W B N R S Q H C P L => [F, W, B, N, R, S, Q, H, C, P, L]

def uniformBoundednessToEventFlow : UniformBoundednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformBoundednessFields x).map uniformBoundednessEncodeBHist

private def uniformBoundednessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformBoundednessEventAt index rest

def uniformBoundednessFromEventFlow (ef : EventFlow) : Option UniformBoundednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformBoundednessUp.mk
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 0 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 1 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 2 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 3 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 4 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 5 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 6 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 7 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 8 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 9 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAt 10 ef)))

private theorem UniformBoundednessTasteGate_single_carrier_alignment_round_trip
    (x : UniformBoundednessUp) :
    uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F W B N R S Q H C P L =>
      change
        some
          (UniformBoundednessUp.mk
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist F))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist W))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist B))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist N))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist R))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist S))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist Q))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist H))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist C))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist P))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist L))) =
          some (UniformBoundednessUp.mk F W B N R S Q H C P L)
      rw [UniformBoundednessTasteGate_single_carrier_alignment_decode_encode F,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode W,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode B,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode N,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode R,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode S,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode Q,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode H,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode C,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode P,
        UniformBoundednessTasteGate_single_carrier_alignment_decode_encode L]

private theorem UniformBoundednessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformBoundednessUp} :
    uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) =
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow y) :=
    congrArg uniformBoundednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformBoundednessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformBoundednessTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformBoundednessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : UniformBoundednessUp,
      uniformBoundednessFields x = uniformBoundednessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ W₁ B₁ N₁ R₁ S₁ Q₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk F₂ W₂ B₂ N₂ R₂ S₂ Q₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance uniformBoundednessBHistCarrier : BHistCarrier UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformBoundednessToEventFlow
  fromEventFlow := uniformBoundednessFromEventFlow

instance uniformBoundednessChapterTasteGate : ChapterTasteGate UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x
    exact UniformBoundednessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformBoundednessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformBoundednessFieldFaithful : FieldFaithful UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformBoundednessFields
  field_faithful := UniformBoundednessTasteGate_single_carrier_alignment_fields_faithful

instance uniformBoundednessNontrivial : Nontrivial UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformBoundednessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformBoundednessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformBoundednessTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h) ∧
      (∀ x : UniformBoundednessUp,
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x) ∧
        (∀ x y : UniformBoundednessUp,
          uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y → x = y) ∧
          uniformBoundednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨UniformBoundednessTasteGate_single_carrier_alignment_decode_encode,
      UniformBoundednessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformBoundednessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformBoundednessUp
