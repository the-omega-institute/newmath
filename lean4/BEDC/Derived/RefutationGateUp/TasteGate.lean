import BEDC.Derived.RefutationGateUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RefutationGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def refutationGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: refutationGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: refutationGateEncodeBHist h

def refutationGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (refutationGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (refutationGateDecodeBHist tail)

private theorem refutationGateDecode_encode :
    ∀ h : BHist, refutationGateDecodeBHist (refutationGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def refutationGateFields : RefutationGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RefutationGateUp.mk Q S B A D T H C P N => [Q, S, B, A, D, T, H, C, P, N]

def refutationGateToEventFlow : RefutationGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map refutationGateEncodeBHist (refutationGateFields x)

def refutationGateFromEventFlow (ef : EventFlow) : Option RefutationGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [Q, S, B, A, D, T, H, C, P, N] =>
      some
        (RefutationGateUp.mk
          (refutationGateDecodeBHist Q)
          (refutationGateDecodeBHist S)
          (refutationGateDecodeBHist B)
          (refutationGateDecodeBHist A)
          (refutationGateDecodeBHist D)
          (refutationGateDecodeBHist T)
          (refutationGateDecodeBHist H)
          (refutationGateDecodeBHist C)
          (refutationGateDecodeBHist P)
          (refutationGateDecodeBHist N))
  | _ => none

private theorem refutationGate_round_trip (x : RefutationGateUp) :
    refutationGateFromEventFlow (refutationGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q S B A D T H C P N =>
      change
        some
          (RefutationGateUp.mk
            (refutationGateDecodeBHist (refutationGateEncodeBHist Q))
            (refutationGateDecodeBHist (refutationGateEncodeBHist S))
            (refutationGateDecodeBHist (refutationGateEncodeBHist B))
            (refutationGateDecodeBHist (refutationGateEncodeBHist A))
            (refutationGateDecodeBHist (refutationGateEncodeBHist D))
            (refutationGateDecodeBHist (refutationGateEncodeBHist T))
            (refutationGateDecodeBHist (refutationGateEncodeBHist H))
            (refutationGateDecodeBHist (refutationGateEncodeBHist C))
            (refutationGateDecodeBHist (refutationGateEncodeBHist P))
            (refutationGateDecodeBHist (refutationGateEncodeBHist N))) =
          some (RefutationGateUp.mk Q S B A D T H C P N)
      rw [refutationGateDecode_encode Q, refutationGateDecode_encode S,
        refutationGateDecode_encode B, refutationGateDecode_encode A,
        refutationGateDecode_encode D, refutationGateDecode_encode T,
        refutationGateDecode_encode H, refutationGateDecode_encode C,
        refutationGateDecode_encode P, refutationGateDecode_encode N]

private theorem refutationGateToEventFlow_injective {x y : RefutationGateUp} :
    refutationGateToEventFlow x = refutationGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      refutationGateFromEventFlow (refutationGateToEventFlow x) =
        refutationGateFromEventFlow (refutationGateToEventFlow y) :=
    congrArg refutationGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (refutationGate_round_trip x).symm
      (Eq.trans hread (refutationGate_round_trip y)))

private theorem refutationGateFieldFaithfulProof :
    ∀ x y : RefutationGateUp, refutationGateFields x = refutationGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 S1 B1 A1 D1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 S2 B2 A2 D2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance refutationGateBHistCarrier : BHistCarrier RefutationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := refutationGateToEventFlow
  fromEventFlow := refutationGateFromEventFlow

instance refutationGateChapterTasteGate : ChapterTasteGate RefutationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change refutationGateFromEventFlow (refutationGateToEventFlow x) = some x
    exact refutationGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (refutationGateToEventFlow_injective heq)

instance refutationGateFieldFaithful : FieldFaithful RefutationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := refutationGateFields
  field_faithful := refutationGateFieldFaithfulProof

instance refutationGateNontrivial : Nontrivial RefutationGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RefutationGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RefutationGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.RefutationGateUp
