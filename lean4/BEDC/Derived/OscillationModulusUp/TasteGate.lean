import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OscillationModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OscillationModulusUp : Type where
  | mk (O U K D W R H C P N : BHist) : OscillationModulusUp
  deriving DecidableEq

def oscillationModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oscillationModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oscillationModulusEncodeBHist h

def oscillationModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oscillationModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oscillationModulusDecodeBHist tail)

private theorem OscillationModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      oscillationModulusDecodeBHist (oscillationModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem OscillationModulusTasteGate_single_carrier_alignment_mk_congr
    {O O' U U' K K' D D' W W' R R' H H' C C' P P' N N' : BHist}
    (hO : O' = O) (hU : U' = U) (hK : K' = K) (hD : D' = D)
    (hW : W' = W) (hR : R' = R) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    OscillationModulusUp.mk O' U' K' D' W' R' H' C' P' N' =
      OscillationModulusUp.mk O U K D W R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hO
  cases hU
  cases hK
  cases hD
  cases hW
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def oscillationModulusFields : OscillationModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OscillationModulusUp.mk O U K D W R H C P N => [O, U, K, D, W, R, H, C, P, N]

def oscillationModulusToEventFlow : OscillationModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oscillationModulusFields x).map oscillationModulusEncodeBHist

private def oscillationModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => oscillationModulusRawAt n rest

private def oscillationModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => oscillationModulusLengthEq n rest

def oscillationModulusFromEventFlow : EventFlow → Option OscillationModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match oscillationModulusLengthEq 10 flow with
      | true =>
          some
            (OscillationModulusUp.mk
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 0 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 1 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 2 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 3 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 4 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 5 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 6 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 7 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 8 flow))
              (oscillationModulusDecodeBHist (oscillationModulusRawAt 9 flow)))
      | false => none

private theorem OscillationModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OscillationModulusUp,
      oscillationModulusFromEventFlow (oscillationModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O U K D W R H C P N =>
      exact
        congrArg some
          (OscillationModulusTasteGate_single_carrier_alignment_mk_congr
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode O)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode U)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode K)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode D)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode W)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode R)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode H)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode C)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode P)
            (OscillationModulusTasteGate_single_carrier_alignment_decode_encode N))

private theorem OscillationModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OscillationModulusUp} :
    oscillationModulusToEventFlow x = oscillationModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oscillationModulusFromEventFlow (oscillationModulusToEventFlow x) =
        oscillationModulusFromEventFlow (oscillationModulusToEventFlow y) :=
    congrArg oscillationModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OscillationModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OscillationModulusTasteGate_single_carrier_alignment_round_trip y)))

instance oscillationModulusBHistCarrier : BHistCarrier OscillationModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oscillationModulusToEventFlow
  fromEventFlow := oscillationModulusFromEventFlow

instance oscillationModulusChapterTasteGate : ChapterTasteGate OscillationModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oscillationModulusFromEventFlow (oscillationModulusToEventFlow x) = some x
    exact OscillationModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OscillationModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem OscillationModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, oscillationModulusDecodeBHist (oscillationModulusEncodeBHist h) = h) ∧
      (∀ x : OscillationModulusUp,
        oscillationModulusFromEventFlow (oscillationModulusToEventFlow x) = some x) ∧
        (∀ x y : OscillationModulusUp,
          oscillationModulusToEventFlow x = oscillationModulusToEventFlow y → x = y) ∧
          oscillationModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨OscillationModulusTasteGate_single_carrier_alignment_decode_encode,
      OscillationModulusTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        OscillationModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.OscillationModulusUp
