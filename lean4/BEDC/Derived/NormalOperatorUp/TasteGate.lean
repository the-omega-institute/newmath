import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalOperatorUp : Type where
  | mk (H I T Tstar A K Q L HT C P N : BHist) : NormalOperatorUp
  deriving DecidableEq

def normalOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalOperatorEncodeBHist h

def normalOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalOperatorDecodeBHist tail)

private theorem normalOperator_decode_encode :
    ∀ h : BHist, normalOperatorDecodeBHist (normalOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normalOperatorFields : NormalOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalOperatorUp.mk H I T Tstar A K Q L HT C P N =>
      [H, I, T, Tstar, A, K, Q, L, HT, C, P, N]

def normalOperatorToEventFlow : NormalOperatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (normalOperatorFields token).map normalOperatorEncodeBHist

def normalOperatorFromEventFlow : EventFlow → Option NormalOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | H :: restH =>
      match restH with
      | I :: restI =>
          match restI with
          | T :: restT =>
              match restT with
              | Tstar :: restTstar =>
                  match restTstar with
                  | A :: restA =>
                      match restA with
                      | K :: restK =>
                          match restK with
                          | Q :: restQ =>
                              match restQ with
                              | L :: restL =>
                                  match restL with
                                  | HT :: restHT =>
                                      match restHT with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (NormalOperatorUp.mk
                                                          (normalOperatorDecodeBHist H)
                                                          (normalOperatorDecodeBHist I)
                                                          (normalOperatorDecodeBHist T)
                                                          (normalOperatorDecodeBHist Tstar)
                                                          (normalOperatorDecodeBHist A)
                                                          (normalOperatorDecodeBHist K)
                                                          (normalOperatorDecodeBHist Q)
                                                          (normalOperatorDecodeBHist L)
                                                          (normalOperatorDecodeBHist HT)
                                                          (normalOperatorDecodeBHist C)
                                                          (normalOperatorDecodeBHist P)
                                                          (normalOperatorDecodeBHist N))
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

private theorem normalOperator_round_trip :
    ∀ token : NormalOperatorUp,
      normalOperatorFromEventFlow (normalOperatorToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk H I T Tstar A K Q L HT C P N =>
      change
        some
            (NormalOperatorUp.mk
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist H))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist I))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist T))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist Tstar))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist A))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist K))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist Q))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist L))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist HT))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist C))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist P))
              (normalOperatorDecodeBHist (normalOperatorEncodeBHist N))) =
          some (NormalOperatorUp.mk H I T Tstar A K Q L HT C P N)
      rw [normalOperator_decode_encode H]
      rw [normalOperator_decode_encode I]
      rw [normalOperator_decode_encode T]
      rw [normalOperator_decode_encode Tstar]
      rw [normalOperator_decode_encode A]
      rw [normalOperator_decode_encode K]
      rw [normalOperator_decode_encode Q]
      rw [normalOperator_decode_encode L]
      rw [normalOperator_decode_encode HT]
      rw [normalOperator_decode_encode C]
      rw [normalOperator_decode_encode P]
      rw [normalOperator_decode_encode N]

private theorem normalOperatorToEventFlow_injective {x y : NormalOperatorUp} :
    normalOperatorToEventFlow x = normalOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalOperatorFromEventFlow (normalOperatorToEventFlow x) =
        normalOperatorFromEventFlow (normalOperatorToEventFlow y) :=
    congrArg normalOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (normalOperator_round_trip x).symm
      (Eq.trans hread (normalOperator_round_trip y)))

instance normalOperatorBHistCarrier : BHistCarrier NormalOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalOperatorToEventFlow
  fromEventFlow := normalOperatorFromEventFlow

instance normalOperatorChapterTasteGate : ChapterTasteGate NormalOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalOperatorFromEventFlow (normalOperatorToEventFlow x) = some x
    exact normalOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (normalOperatorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NormalOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalOperatorChapterTasteGate

theorem NormalOperatorTasteGate_single_carrier_alignment :
    ∃ x y : NormalOperatorUp,
      x ≠ y ∧
        normalOperatorFromEventFlow (normalOperatorToEventFlow x) = some x ∧
          normalOperatorFromEventFlow (normalOperatorToEventFlow y) = some y := by
  -- BEDC touchpoint anchor: BHist BMark
  let x :=
    NormalOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  let y :=
    NormalOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty
  refine ⟨x, y, ?_, normalOperator_round_trip x, normalOperator_round_trip y⟩
  intro h
  injection h with hHead
  cases hHead

end BEDC.Derived.NormalOperatorUp
