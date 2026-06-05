import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalInductionGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalInductionGateUp : Type where
  | mk : (S O M Pi F Cn B Y H R P N : BHist) → PhysicalInductionGateUp
  deriving DecidableEq

def physicalInductionGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalInductionGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalInductionGateEncodeBHist h

def physicalInductionGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalInductionGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalInductionGateDecodeBHist tail)

private theorem physicalInductionGateDecode_encode_bhist :
    ∀ h : BHist, physicalInductionGateDecodeBHist
      (physicalInductionGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def physicalInductionGateFields :
    PhysicalInductionGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalInductionGateUp.mk S O M Pi F Cn B Y H R P N =>
      [S, O, M, Pi, F, Cn, B, Y, H, R, P, N]

def physicalInductionGateToEventFlow :
    PhysicalInductionGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (physicalInductionGateFields x).map physicalInductionGateEncodeBHist

def physicalInductionGateFromEventFlow :
    EventFlow → Option PhysicalInductionGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, O, M, Pi, F, Cn, B, Y, H, R, P, N] =>
      some
        (PhysicalInductionGateUp.mk
          (physicalInductionGateDecodeBHist S)
          (physicalInductionGateDecodeBHist O)
          (physicalInductionGateDecodeBHist M)
          (physicalInductionGateDecodeBHist Pi)
          (physicalInductionGateDecodeBHist F)
          (physicalInductionGateDecodeBHist Cn)
          (physicalInductionGateDecodeBHist B)
          (physicalInductionGateDecodeBHist Y)
          (physicalInductionGateDecodeBHist H)
          (physicalInductionGateDecodeBHist R)
          (physicalInductionGateDecodeBHist P)
          (physicalInductionGateDecodeBHist N))
  | _ => none

private theorem physicalInductionGate_round_trip :
    ∀ x : PhysicalInductionGateUp,
      physicalInductionGateFromEventFlow (physicalInductionGateToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S O M Pi F Cn B Y H R P N =>
      change
        some
          (PhysicalInductionGateUp.mk
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist S))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist O))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist M))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist Pi))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist F))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist Cn))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist B))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist Y))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist H))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist R))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist P))
            (physicalInductionGateDecodeBHist (physicalInductionGateEncodeBHist N))) =
          some (PhysicalInductionGateUp.mk S O M Pi F Cn B Y H R P N)
      rw [physicalInductionGateDecode_encode_bhist S,
        physicalInductionGateDecode_encode_bhist O,
        physicalInductionGateDecode_encode_bhist M,
        physicalInductionGateDecode_encode_bhist Pi,
        physicalInductionGateDecode_encode_bhist F,
        physicalInductionGateDecode_encode_bhist Cn,
        physicalInductionGateDecode_encode_bhist B,
        physicalInductionGateDecode_encode_bhist Y,
        physicalInductionGateDecode_encode_bhist H,
        physicalInductionGateDecode_encode_bhist R,
        physicalInductionGateDecode_encode_bhist P,
        physicalInductionGateDecode_encode_bhist N]

private theorem physicalInductionGateToEventFlow_injective
    {x y : PhysicalInductionGateUp} :
    physicalInductionGateToEventFlow x = physicalInductionGateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalInductionGateFromEventFlow (physicalInductionGateToEventFlow x) =
        physicalInductionGateFromEventFlow (physicalInductionGateToEventFlow y) :=
    congrArg physicalInductionGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalInductionGate_round_trip x).symm
      (Eq.trans hread (physicalInductionGate_round_trip y)))

private theorem physicalInductionGate_field_faithful :
    ∀ x y : PhysicalInductionGateUp,
      physicalInductionGateFields x = physicalInductionGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S O M Pi F Cn B Y H R P N =>
      cases y with
      | mk S' O' M' Pi' F' Cn' B' Y' H' R' P' N' =>
          cases hfields
          rfl

instance physicalInductionGateBHistCarrier :
    BHistCarrier PhysicalInductionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalInductionGateToEventFlow
  fromEventFlow := physicalInductionGateFromEventFlow

instance physicalInductionGateChapterTasteGate :
    ChapterTasteGate PhysicalInductionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicalInductionGateFromEventFlow (physicalInductionGateToEventFlow x) =
      some x
    exact physicalInductionGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalInductionGateToEventFlow_injective heq)

instance physicalInductionGateFieldFaithful :
    FieldFaithful PhysicalInductionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalInductionGateFields
  field_faithful := physicalInductionGate_field_faithful

instance physicalInductionGateNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PhysicalInductionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalInductionGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PhysicalInductionGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalInductionGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalInductionGateChapterTasteGate

end BEDC.Derived.PhysicalInductionGateUp
