import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RatCauchyCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RatCauchyCompletionUp : Type where
  | mk (R M S Q D E H K P N : BHist) : RatCauchyCompletionUp
  deriving DecidableEq

def ratCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ratCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ratCauchyCompletionEncodeBHist h

def ratCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ratCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ratCauchyCompletionDecodeBHist tail)

private theorem ratCauchyCompletionDecode_encode_bhist :
    ∀ h : BHist, ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ratCauchyCompletionFields : RatCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RatCauchyCompletionUp.mk R M S Q D E H K P N => [R, M, S, Q, D, E, H, K, P, N]

def ratCauchyCompletionToEventFlow : RatCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ratCauchyCompletionFields x).map ratCauchyCompletionEncodeBHist

def ratCauchyCompletionFromEventFlow : EventFlow → Option RatCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: restM =>
      match restM with
      | [] => none
      | M :: restS =>
          match restS with
          | [] => none
          | S :: restQ =>
              match restQ with
              | [] => none
              | Q :: restD =>
                  match restD with
                  | [] => none
                  | D :: restE =>
                      match restE with
                      | [] => none
                      | E :: restH =>
                          match restH with
                          | [] => none
                          | H :: restK =>
                              match restK with
                              | [] => none
                              | K :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (RatCauchyCompletionUp.mk
                                                  (ratCauchyCompletionDecodeBHist R)
                                                  (ratCauchyCompletionDecodeBHist M)
                                                  (ratCauchyCompletionDecodeBHist S)
                                                  (ratCauchyCompletionDecodeBHist Q)
                                                  (ratCauchyCompletionDecodeBHist D)
                                                  (ratCauchyCompletionDecodeBHist E)
                                                  (ratCauchyCompletionDecodeBHist H)
                                                  (ratCauchyCompletionDecodeBHist K)
                                                  (ratCauchyCompletionDecodeBHist P)
                                                  (ratCauchyCompletionDecodeBHist N))
                                          | _ :: _ => none

private theorem ratCauchyCompletion_round_trip :
    ∀ x : RatCauchyCompletionUp,
      ratCauchyCompletionFromEventFlow (ratCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M S Q D E H K P N =>
      change
        some
          (RatCauchyCompletionUp.mk
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist R))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist M))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist S))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist Q))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist D))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist E))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist H))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist K))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist P))
            (ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist N))) =
          some (RatCauchyCompletionUp.mk R M S Q D E H K P N)
      rw [ratCauchyCompletionDecode_encode_bhist R, ratCauchyCompletionDecode_encode_bhist M,
        ratCauchyCompletionDecode_encode_bhist S, ratCauchyCompletionDecode_encode_bhist Q,
        ratCauchyCompletionDecode_encode_bhist D, ratCauchyCompletionDecode_encode_bhist E,
        ratCauchyCompletionDecode_encode_bhist H, ratCauchyCompletionDecode_encode_bhist K,
        ratCauchyCompletionDecode_encode_bhist P, ratCauchyCompletionDecode_encode_bhist N]

private theorem ratCauchyCompletionToEventFlow_injective {x y : RatCauchyCompletionUp} :
    ratCauchyCompletionToEventFlow x = ratCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ratCauchyCompletionFromEventFlow (ratCauchyCompletionToEventFlow x) =
        ratCauchyCompletionFromEventFlow (ratCauchyCompletionToEventFlow y) :=
    congrArg ratCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ratCauchyCompletion_round_trip x).symm
      (Eq.trans hread (ratCauchyCompletion_round_trip y)))

instance ratCauchyCompletionBHistCarrier : BHistCarrier RatCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ratCauchyCompletionToEventFlow
  fromEventFlow := ratCauchyCompletionFromEventFlow

instance ratCauchyCompletionChapterTasteGate : ChapterTasteGate RatCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ratCauchyCompletionFromEventFlow (ratCauchyCompletionToEventFlow x) = some x
    exact ratCauchyCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ratCauchyCompletionToEventFlow_injective heq)

theorem RatCauchyCompletionCarrier_namecert_obligations :
    Nonempty (ChapterTasteGate RatCauchyCompletionUp) ∧
      (∀ h : BHist, ratCauchyCompletionDecodeBHist (ratCauchyCompletionEncodeBHist h) = h) ∧
        (∀ x : RatCauchyCompletionUp,
          ratCauchyCompletionFromEventFlow (ratCauchyCompletionToEventFlow x) = some x) ∧
          ratCauchyCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨ratCauchyCompletionChapterTasteGate⟩
  · constructor
    · exact ratCauchyCompletionDecode_encode_bhist
    · constructor
      · exact ratCauchyCompletion_round_trip
      · rfl

end BEDC.Derived.RatCauchyCompletionUp.TasteGate
