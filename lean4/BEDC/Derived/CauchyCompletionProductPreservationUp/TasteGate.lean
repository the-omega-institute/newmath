import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionProductPreservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionProductPreservationUp : Type where
  | mk (L R M Pi S E H C P N : BHist) : CauchyCompletionProductPreservationUp
  deriving DecidableEq

def cauchyCompletionProductPreservationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionProductPreservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionProductPreservationEncodeBHist h

def cauchyCompletionProductPreservationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionProductPreservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionProductPreservationDecodeBHist tail)

private theorem cauchyCompletionProductPreservation_decode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionProductPreservationDecodeBHist
        (cauchyCompletionProductPreservationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cauchyCompletionProductPreservation_mk_congr
    {L L' R R' M M' Pi Pi' S S' E E' H H' C C' P P' N N' : BHist}
    (hL : L' = L) (hR : R' = R) (hM : M' = M) (hPi : Pi' = Pi)
    (hS : S' = S) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyCompletionProductPreservationUp.mk L' R' M' Pi' S' E' H' C' P' N' =
      CauchyCompletionProductPreservationUp.mk L R M Pi S E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hR
  cases hM
  cases hPi
  cases hS
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyCompletionProductPreservationFields :
    CauchyCompletionProductPreservationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionProductPreservationUp.mk L R M Pi S E H C P N =>
      [L, R, M, Pi, S, E, H, C, P, N]

def cauchyCompletionProductPreservationToEventFlow :
    CauchyCompletionProductPreservationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionProductPreservationFields x).map
        cauchyCompletionProductPreservationEncodeBHist

private def cauchyCompletionProductPreservationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyCompletionProductPreservationRawAt n rest

private def cauchyCompletionProductPreservationLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyCompletionProductPreservationLengthEq n rest

def cauchyCompletionProductPreservationFromEventFlow :
    EventFlow → Option CauchyCompletionProductPreservationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyCompletionProductPreservationLengthEq 10 flow with
      | true =>
          some
            (CauchyCompletionProductPreservationUp.mk
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 0 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 1 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 2 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 3 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 4 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 5 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 6 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 7 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 8 flow))
              (cauchyCompletionProductPreservationDecodeBHist
                (cauchyCompletionProductPreservationRawAt 9 flow)))
      | false => none

private theorem cauchyCompletionProductPreservation_round_trip :
    ∀ x : CauchyCompletionProductPreservationUp,
      cauchyCompletionProductPreservationFromEventFlow
        (cauchyCompletionProductPreservationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R M Pi S E H C P N =>
      exact
        congrArg some
          (cauchyCompletionProductPreservation_mk_congr
            (cauchyCompletionProductPreservation_decode_encode_bhist L)
            (cauchyCompletionProductPreservation_decode_encode_bhist R)
            (cauchyCompletionProductPreservation_decode_encode_bhist M)
            (cauchyCompletionProductPreservation_decode_encode_bhist Pi)
            (cauchyCompletionProductPreservation_decode_encode_bhist S)
            (cauchyCompletionProductPreservation_decode_encode_bhist E)
            (cauchyCompletionProductPreservation_decode_encode_bhist H)
            (cauchyCompletionProductPreservation_decode_encode_bhist C)
            (cauchyCompletionProductPreservation_decode_encode_bhist P)
            (cauchyCompletionProductPreservation_decode_encode_bhist N))

private theorem cauchyCompletionProductPreservationToEventFlow_injective
    {x y : CauchyCompletionProductPreservationUp} :
    cauchyCompletionProductPreservationToEventFlow x =
      cauchyCompletionProductPreservationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionProductPreservationFromEventFlow
          (cauchyCompletionProductPreservationToEventFlow x) =
        cauchyCompletionProductPreservationFromEventFlow
          (cauchyCompletionProductPreservationToEventFlow y) :=
    congrArg cauchyCompletionProductPreservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionProductPreservation_round_trip x).symm
      (Eq.trans hread (cauchyCompletionProductPreservation_round_trip y)))

instance cauchyCompletionProductPreservationBHistCarrier :
    BHistCarrier CauchyCompletionProductPreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionProductPreservationToEventFlow
  fromEventFlow := cauchyCompletionProductPreservationFromEventFlow

instance cauchyCompletionProductPreservationChapterTasteGate :
    ChapterTasteGate CauchyCompletionProductPreservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionProductPreservationFromEventFlow
        (cauchyCompletionProductPreservationToEventFlow x) = some x
    exact cauchyCompletionProductPreservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionProductPreservationToEventFlow_injective heq)

theorem CauchyCompletionProductPreservationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionProductPreservationDecodeBHist
        (cauchyCompletionProductPreservationEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionProductPreservationUp,
        cauchyCompletionProductPreservationFromEventFlow
          (cauchyCompletionProductPreservationToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionProductPreservationUp,
          cauchyCompletionProductPreservationToEventFlow x =
            cauchyCompletionProductPreservationToEventFlow y → x = y) ∧
          cauchyCompletionProductPreservationEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyCompletionProductPreservation_decode_encode_bhist,
      cauchyCompletionProductPreservation_round_trip,
      (fun _ _ heq => cauchyCompletionProductPreservationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionProductPreservationUp
