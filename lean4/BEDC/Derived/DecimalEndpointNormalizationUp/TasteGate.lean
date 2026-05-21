import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalEndpointNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalEndpointNormalizationUp : Type where
  | mk (D E L A W Q R S H C P N : BHist) : DecimalEndpointNormalizationUp
  deriving DecidableEq

def decimalEndpointNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalEndpointNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalEndpointNormalizationEncodeBHist h

def decimalEndpointNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalEndpointNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalEndpointNormalizationDecodeBHist tail)

private theorem decimalEndpointNormalization_decode_encode :
    ∀ h : BHist,
      decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem DecimalEndpointNormalizationTasteGate_single_carrier_alignment_mk_congr
    {D D' E E' L L' A A' W W' Q Q' R R' S S' H H' C C' P P' N N' : BHist}
    (hD : D = D') (hE : E = E') (hL : L = L') (hA : A = A')
    (hW : W = W') (hQ : Q = Q') (hR : R = R') (hS : S = S')
    (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    DecimalEndpointNormalizationUp.mk D E L A W Q R S H C P N =
      DecimalEndpointNormalizationUp.mk D' E' L' A' W' Q' R' S' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hE
  cases hL
  cases hA
  cases hW
  cases hQ
  cases hR
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def decimalEndpointNormalizationFields :
    DecimalEndpointNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalEndpointNormalizationUp.mk D E L A W Q R S H C P N =>
      [D, E, L, A, W, Q, R, S, H, C, P, N]

def decimalEndpointNormalizationToEventFlow :
    DecimalEndpointNormalizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (decimalEndpointNormalizationFields x).map decimalEndpointNormalizationEncodeBHist

def decimalEndpointNormalizationFromEventFlow :
    EventFlow → Option DecimalEndpointNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: restD =>
      match restD with
      | E :: restE =>
          match restE with
          | L :: restL =>
              match restL with
              | A :: restA =>
                  match restA with
                  | W :: restW =>
                      match restW with
                      | Q :: restQ =>
                          match restQ with
                          | R :: restR =>
                              match restR with
                              | S :: restS =>
                                  match restS with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (DecimalEndpointNormalizationUp.mk
                                                          (decimalEndpointNormalizationDecodeBHist D)
                                                          (decimalEndpointNormalizationDecodeBHist E)
                                                          (decimalEndpointNormalizationDecodeBHist L)
                                                          (decimalEndpointNormalizationDecodeBHist A)
                                                          (decimalEndpointNormalizationDecodeBHist W)
                                                          (decimalEndpointNormalizationDecodeBHist Q)
                                                          (decimalEndpointNormalizationDecodeBHist R)
                                                          (decimalEndpointNormalizationDecodeBHist S)
                                                          (decimalEndpointNormalizationDecodeBHist H)
                                                          (decimalEndpointNormalizationDecodeBHist C)
                                                          (decimalEndpointNormalizationDecodeBHist P)
                                                          (decimalEndpointNormalizationDecodeBHist N))
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

private theorem decimalEndpointNormalization_round_trip :
    ∀ x : DecimalEndpointNormalizationUp,
      decimalEndpointNormalizationFromEventFlow (decimalEndpointNormalizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D E L A W Q R S H C P N =>
      change
        some
            (DecimalEndpointNormalizationUp.mk
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist D))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist E))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist L))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist A))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist W))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist Q))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist R))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist S))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist H))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist C))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist P))
              (decimalEndpointNormalizationDecodeBHist
                (decimalEndpointNormalizationEncodeBHist N))) =
          some (DecimalEndpointNormalizationUp.mk D E L A W Q R S H C P N)
      exact
        congrArg some
          (DecimalEndpointNormalizationTasteGate_single_carrier_alignment_mk_congr
            (decimalEndpointNormalization_decode_encode D)
            (decimalEndpointNormalization_decode_encode E)
            (decimalEndpointNormalization_decode_encode L)
            (decimalEndpointNormalization_decode_encode A)
            (decimalEndpointNormalization_decode_encode W)
            (decimalEndpointNormalization_decode_encode Q)
            (decimalEndpointNormalization_decode_encode R)
            (decimalEndpointNormalization_decode_encode S)
            (decimalEndpointNormalization_decode_encode H)
            (decimalEndpointNormalization_decode_encode C)
            (decimalEndpointNormalization_decode_encode P)
            (decimalEndpointNormalization_decode_encode N))

private theorem decimalEndpointNormalizationToEventFlow_injective
    {x y : DecimalEndpointNormalizationUp} :
    decimalEndpointNormalizationToEventFlow x =
        decimalEndpointNormalizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          decimalEndpointNormalizationFromEventFlow
            (decimalEndpointNormalizationToEventFlow x) :=
        (decimalEndpointNormalization_round_trip x).symm
      _ =
          decimalEndpointNormalizationFromEventFlow
            (decimalEndpointNormalizationToEventFlow y) :=
        congrArg decimalEndpointNormalizationFromEventFlow hxy
      _ = some y := decimalEndpointNormalization_round_trip y
  exact Option.some.inj optionEq

instance decimalEndpointNormalizationBHistCarrier :
    BHistCarrier DecimalEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalEndpointNormalizationToEventFlow
  fromEventFlow := decimalEndpointNormalizationFromEventFlow

instance decimalEndpointNormalizationChapterTasteGate :
    ChapterTasteGate DecimalEndpointNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      decimalEndpointNormalizationFromEventFlow (decimalEndpointNormalizationToEventFlow x) =
        some x
    exact decimalEndpointNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (decimalEndpointNormalizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DecimalEndpointNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  decimalEndpointNormalizationChapterTasteGate

theorem DecimalEndpointNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      decimalEndpointNormalizationDecodeBHist (decimalEndpointNormalizationEncodeBHist h) =
        h) ∧
      (∀ x : DecimalEndpointNormalizationUp,
        decimalEndpointNormalizationFromEventFlow
            (decimalEndpointNormalizationToEventFlow x) =
          some x) ∧
      (∀ x y : DecimalEndpointNormalizationUp,
        decimalEndpointNormalizationToEventFlow x =
            decimalEndpointNormalizationToEventFlow y →
          x = y) ∧
      decimalEndpointNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨decimalEndpointNormalization_decode_encode,
      decimalEndpointNormalization_round_trip,
      (fun _ _ heq => decimalEndpointNormalizationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DecimalEndpointNormalizationUp
