import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyConvergenceModulusTailMonotonicityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyConvergenceModulusTailMonotonicityUp : Type where
  | mk (K T W R D L H C P N : BHist) : CauchyConvergenceModulusTailMonotonicityUp
  deriving DecidableEq

def cauchyConvergenceModulusTailMonotonicityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyConvergenceModulusTailMonotonicityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyConvergenceModulusTailMonotonicityEncodeBHist h

def cauchyConvergenceModulusTailMonotonicityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyConvergenceModulusTailMonotonicityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyConvergenceModulusTailMonotonicityDecodeBHist tail)

private theorem cauchyConvergenceModulusTailMonotonicity_decode_encode :
    ∀ h : BHist,
      cauchyConvergenceModulusTailMonotonicityDecodeBHist
        (cauchyConvergenceModulusTailMonotonicityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyConvergenceModulusTailMonotonicityFields :
    CauchyConvergenceModulusTailMonotonicityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyConvergenceModulusTailMonotonicityUp.mk K T W R D L H C P N =>
      [K, T, W, R, D, L, H, C, P, N]

def cauchyConvergenceModulusTailMonotonicityToEventFlow :
    CauchyConvergenceModulusTailMonotonicityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyConvergenceModulusTailMonotonicityFields x).map
        cauchyConvergenceModulusTailMonotonicityEncodeBHist

private def cauchyConvergenceModulusTailMonotonicityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyConvergenceModulusTailMonotonicityRawAt n rest

private def cauchyConvergenceModulusTailMonotonicityLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyConvergenceModulusTailMonotonicityLengthEq n rest

def cauchyConvergenceModulusTailMonotonicityFromEventFlow :
    EventFlow → Option CauchyConvergenceModulusTailMonotonicityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyConvergenceModulusTailMonotonicityLengthEq 10 flow with
      | true =>
          some
            (CauchyConvergenceModulusTailMonotonicityUp.mk
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 0 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 1 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 2 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 3 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 4 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 5 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 6 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 7 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 8 flow))
              (cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityRawAt 9 flow)))
      | false => none

private theorem cauchyConvergenceModulusTailMonotonicity_mk_congr
    {K K' T T' W W' R R' D D' L L' H H' C C' P P' N N' : BHist}
    (hK : K' = K) (hT : T' = T) (hW : W' = W) (hR : R' = R)
    (hD : D' = D) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyConvergenceModulusTailMonotonicityUp.mk K' T' W' R' D' L' H' C' P' N' =
      CauchyConvergenceModulusTailMonotonicityUp.mk K T W R D L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hT
  cases hW
  cases hR
  cases hD
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem cauchyConvergenceModulusTailMonotonicity_round_trip :
    ∀ x : CauchyConvergenceModulusTailMonotonicityUp,
      cauchyConvergenceModulusTailMonotonicityFromEventFlow
        (cauchyConvergenceModulusTailMonotonicityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T W R D L H C P N =>
      exact
        congrArg some
          (cauchyConvergenceModulusTailMonotonicity_mk_congr
            (cauchyConvergenceModulusTailMonotonicity_decode_encode K)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode T)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode W)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode R)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode D)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode L)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode H)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode C)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode P)
            (cauchyConvergenceModulusTailMonotonicity_decode_encode N))

private theorem cauchyConvergenceModulusTailMonotonicityToEventFlow_injective
    {x y : CauchyConvergenceModulusTailMonotonicityUp} :
    cauchyConvergenceModulusTailMonotonicityToEventFlow x =
      cauchyConvergenceModulusTailMonotonicityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow x) =
        cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow y) :=
    congrArg cauchyConvergenceModulusTailMonotonicityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyConvergenceModulusTailMonotonicity_round_trip x).symm
      (Eq.trans hread (cauchyConvergenceModulusTailMonotonicity_round_trip y)))

instance cauchyConvergenceModulusTailMonotonicityBHistCarrier :
    BHistCarrier CauchyConvergenceModulusTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyConvergenceModulusTailMonotonicityToEventFlow
  fromEventFlow := cauchyConvergenceModulusTailMonotonicityFromEventFlow

instance cauchyConvergenceModulusTailMonotonicityChapterTasteGate :
    ChapterTasteGate CauchyConvergenceModulusTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyConvergenceModulusTailMonotonicityFromEventFlow
        (cauchyConvergenceModulusTailMonotonicityToEventFlow x) = some x
    exact cauchyConvergenceModulusTailMonotonicity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyConvergenceModulusTailMonotonicityToEventFlow_injective heq)

theorem CauchyConvergenceModulusTailMonotonicityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyConvergenceModulusTailMonotonicityDecodeBHist
        (cauchyConvergenceModulusTailMonotonicityEncodeBHist h) = h) ∧
      (∀ x : CauchyConvergenceModulusTailMonotonicityUp,
        cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow x) = some x) ∧
        (∀ x y : CauchyConvergenceModulusTailMonotonicityUp,
          cauchyConvergenceModulusTailMonotonicityToEventFlow x =
            cauchyConvergenceModulusTailMonotonicityToEventFlow y → x = y) ∧
          cauchyConvergenceModulusTailMonotonicityEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyConvergenceModulusTailMonotonicity_decode_encode,
      cauchyConvergenceModulusTailMonotonicity_round_trip,
      (fun _ _ heq => cauchyConvergenceModulusTailMonotonicityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyConvergenceModulusTailMonotonicityUp
