import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimitiveRecursionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimitiveRecursionUp : Type where
  | mk : (D S T U W Q H C P N : BHist) → PrimitiveRecursionUp
  deriving DecidableEq

def primitiveRecursionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primitiveRecursionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primitiveRecursionEncodeBHist h

def primitiveRecursionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primitiveRecursionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primitiveRecursionDecodeBHist tail)

private theorem primitiveRecursion_decode_encode :
    ∀ h : BHist, primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def primitiveRecursionFields : PrimitiveRecursionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrimitiveRecursionUp.mk D S T U W Q H C P N => [D, S, T, U, W, Q, H, C, P, N]

def primitiveRecursionToEventFlow : PrimitiveRecursionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (primitiveRecursionFields x).map primitiveRecursionEncodeBHist

def primitiveRecursionFromEventFlow : EventFlow → Option PrimitiveRecursionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (PrimitiveRecursionUp.mk
                                                  (primitiveRecursionDecodeBHist D)
                                                  (primitiveRecursionDecodeBHist S)
                                                  (primitiveRecursionDecodeBHist T)
                                                  (primitiveRecursionDecodeBHist U)
                                                  (primitiveRecursionDecodeBHist W)
                                                  (primitiveRecursionDecodeBHist Q)
                                                  (primitiveRecursionDecodeBHist H)
                                                  (primitiveRecursionDecodeBHist C)
                                                  (primitiveRecursionDecodeBHist P)
                                                  (primitiveRecursionDecodeBHist N))
                                          | _ :: _ => none

private theorem primitiveRecursion_round_trip :
    ∀ x : PrimitiveRecursionUp,
      primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S T U W Q H C P N =>
      change
        some
          (PrimitiveRecursionUp.mk
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist D))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist S))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist T))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist U))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist W))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist Q))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist H))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist C))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist P))
            (primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist N))) =
          some (PrimitiveRecursionUp.mk D S T U W Q H C P N)
      rw [primitiveRecursion_decode_encode D, primitiveRecursion_decode_encode S,
        primitiveRecursion_decode_encode T, primitiveRecursion_decode_encode U,
        primitiveRecursion_decode_encode W, primitiveRecursion_decode_encode Q,
        primitiveRecursion_decode_encode H, primitiveRecursion_decode_encode C,
        primitiveRecursion_decode_encode P, primitiveRecursion_decode_encode N]

private theorem primitiveRecursionToEventFlow_injective
    {x y : PrimitiveRecursionUp} :
    primitiveRecursionToEventFlow x = primitiveRecursionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) =
        primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow y) :=
    congrArg primitiveRecursionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (primitiveRecursion_round_trip x).symm
      (Eq.trans hread (primitiveRecursion_round_trip y)))

private theorem primitiveRecursion_fields_faithful :
    ∀ x y : PrimitiveRecursionUp,
      primitiveRecursionFields x = primitiveRecursionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D1 S1 T1 U1 W1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 T2 U2 W2 Q2 H2 C2 P2 N2 =>
          injection h with hD t1
          injection t1 with hS t2
          injection t2 with hT t3
          injection t3 with hU t4
          injection t4 with hW t5
          injection t5 with hQ t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hD
          subst hS
          subst hT
          subst hU
          subst hW
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance primitiveRecursionBHistCarrier : BHistCarrier PrimitiveRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primitiveRecursionToEventFlow
  fromEventFlow := primitiveRecursionFromEventFlow

instance primitiveRecursionChapterTasteGate :
    ChapterTasteGate PrimitiveRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) = some x
    exact primitiveRecursion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (primitiveRecursionToEventFlow_injective heq)

instance primitiveRecursionFieldFaithful : FieldFaithful PrimitiveRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := primitiveRecursionFields
  field_faithful := primitiveRecursion_fields_faithful

instance primitiveRecursionNontrivial : Nontrivial PrimitiveRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrimitiveRecursionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrimitiveRecursionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PrimitiveRecursionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primitiveRecursionChapterTasteGate

theorem PrimitiveRecursionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PrimitiveRecursionUp) ∧
      Nonempty (FieldFaithful PrimitiveRecursionUp) ∧
      Nonempty (Nontrivial PrimitiveRecursionUp) ∧
      (∀ h : BHist, primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist h) = h) ∧
      (∀ x : PrimitiveRecursionUp,
        primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) = some x) ∧
      (∀ x y : PrimitiveRecursionUp,
        primitiveRecursionToEventFlow x = primitiveRecursionToEventFlow y → x = y) ∧
      primitiveRecursionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨primitiveRecursionChapterTasteGate⟩, ⟨primitiveRecursionFieldFaithful⟩,
      ⟨primitiveRecursionNontrivial⟩, primitiveRecursion_decode_encode,
      primitiveRecursion_round_trip,
      fun _ _ heq => primitiveRecursionToEventFlow_injective heq, rfl⟩

end BEDC.Derived.PrimitiveRecursionUp.TasteGate
