import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AdjointOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AdjointOperatorUp : Type where
  | mk (H K T Ts B Bs IH IK J L P N : BHist) : AdjointOperatorUp
  deriving DecidableEq

def adjointOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: adjointOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: adjointOperatorEncodeBHist h

def adjointOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (adjointOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (adjointOperatorDecodeBHist tail)

private theorem adjointOperator_decode_encode :
    ∀ h : BHist, adjointOperatorDecodeBHist (adjointOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def adjointOperatorFields : AdjointOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AdjointOperatorUp.mk H K T Ts B Bs IH IK J L P N => [H, K, T, Ts, B, Bs, IH, IK, J, L, P, N]

def adjointOperatorToEventFlow : AdjointOperatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (adjointOperatorFields token).map adjointOperatorEncodeBHist

def adjointOperatorFromEventFlow : EventFlow → Option AdjointOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | H :: restH =>
      match restH with
      | K :: restK =>
          match restK with
          | T :: restT =>
              match restT with
              | Ts :: restTs =>
                  match restTs with
                  | B :: restB =>
                      match restB with
                      | Bs :: restBs =>
                          match restBs with
                          | IH :: restIH =>
                              match restIH with
                              | IK :: restIK =>
                                  match restIK with
                                  | J :: restJ =>
                                      match restJ with
                                      | L :: restL =>
                                          match restL with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (AdjointOperatorUp.mk
                                                          (adjointOperatorDecodeBHist H)
                                                          (adjointOperatorDecodeBHist K)
                                                          (adjointOperatorDecodeBHist T)
                                                          (adjointOperatorDecodeBHist Ts)
                                                          (adjointOperatorDecodeBHist B)
                                                          (adjointOperatorDecodeBHist Bs)
                                                          (adjointOperatorDecodeBHist IH)
                                                          (adjointOperatorDecodeBHist IK)
                                                          (adjointOperatorDecodeBHist J)
                                                          (adjointOperatorDecodeBHist L)
                                                          (adjointOperatorDecodeBHist P)
                                                          (adjointOperatorDecodeBHist N))
                                                  | _ :: _ => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem adjointOperator_round_trip :
    ∀ token : AdjointOperatorUp,
      adjointOperatorFromEventFlow (adjointOperatorToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk H K T Ts B Bs IH IK J L P N =>
      change
        some
            (AdjointOperatorUp.mk
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist H))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist K))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist T))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist Ts))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist B))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist Bs))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist IH))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist IK))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist J))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist L))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist P))
              (adjointOperatorDecodeBHist (adjointOperatorEncodeBHist N))) =
          some (AdjointOperatorUp.mk H K T Ts B Bs IH IK J L P N)
      rw [adjointOperator_decode_encode H]
      rw [adjointOperator_decode_encode K]
      rw [adjointOperator_decode_encode T]
      rw [adjointOperator_decode_encode Ts]
      rw [adjointOperator_decode_encode B]
      rw [adjointOperator_decode_encode Bs]
      rw [adjointOperator_decode_encode IH]
      rw [adjointOperator_decode_encode IK]
      rw [adjointOperator_decode_encode J]
      rw [adjointOperator_decode_encode L]
      rw [adjointOperator_decode_encode P]
      rw [adjointOperator_decode_encode N]

private theorem adjointOperatorToEventFlow_injective {x y : AdjointOperatorUp} :
    adjointOperatorToEventFlow x = adjointOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      adjointOperatorFromEventFlow (adjointOperatorToEventFlow x) =
        adjointOperatorFromEventFlow (adjointOperatorToEventFlow y) :=
    congrArg adjointOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (adjointOperator_round_trip x).symm
      (Eq.trans hread (adjointOperator_round_trip y)))

instance adjointOperatorBHistCarrier : BHistCarrier AdjointOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := adjointOperatorToEventFlow
  fromEventFlow := adjointOperatorFromEventFlow

instance adjointOperatorChapterTasteGate : ChapterTasteGate AdjointOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change adjointOperatorFromEventFlow (adjointOperatorToEventFlow x) = some x
    exact adjointOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (adjointOperatorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AdjointOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  adjointOperatorChapterTasteGate

theorem AdjointOperatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, adjointOperatorDecodeBHist (adjointOperatorEncodeBHist h) = h) ∧
      (∀ x : AdjointOperatorUp,
        adjointOperatorFromEventFlow (adjointOperatorToEventFlow x) = some x) ∧
      (∀ x y : AdjointOperatorUp,
        adjointOperatorToEventFlow x = adjointOperatorToEventFlow y → x = y) ∧
      ∃ x : AdjointOperatorUp,
        x =
          AdjointOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty ∧
        adjointOperatorFromEventFlow (adjointOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact adjointOperator_decode_encode
  constructor
  · intro x
    exact adjointOperator_round_trip x
  constructor
  · intro x y heq
    exact adjointOperatorToEventFlow_injective heq
  · let token :=
      AdjointOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    exact ⟨token, rfl, adjointOperator_round_trip token⟩

end BEDC.Derived.AdjointOperatorUp
