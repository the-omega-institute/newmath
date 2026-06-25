import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRecursionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRecursionUp : Type where
  | mk (Q S D E L H C P N : BHist) : RegularCauchyRecursionUp
  deriving DecidableEq

def regularCauchyRecursionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRecursionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRecursionEncodeBHist h

def regularCauchyRecursionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRecursionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRecursionDecodeBHist tail)

private theorem RegularCauchyRecursionTasteGate_decode_encode :
    ∀ h : BHist,
      regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RegularCauchyRecursionTasteGate_mk_congr
    {Q Q' S S' D D' E E' L L' H H' C C' P P' N N' : BHist}
    (hQ : Q = Q') (hS : S = S') (hD : D = D') (hE : E = E') (hL : L = L')
    (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    RegularCauchyRecursionUp.mk Q S D E L H C P N =
      RegularCauchyRecursionUp.mk Q' S' D' E' L' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hS
  cases hD
  cases hE
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyRecursionFields : RegularCauchyRecursionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRecursionUp.mk Q S D E L H C P N => [Q, S, D, E, L, H, C, P, N]

def regularCauchyRecursionToEventFlow : RegularCauchyRecursionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyRecursionFields x).map regularCauchyRecursionEncodeBHist

def regularCauchyRecursionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => regularCauchyRecursionEventAt n rest
  | _, [] => []

def regularCauchyRecursionFromEventFlow (ef : EventFlow) : Option RegularCauchyRecursionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyRecursionUp.mk
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 0 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 1 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 2 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 3 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 4 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 5 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 6 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 7 ef))
      (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEventAt 8 ef)))

private theorem RegularCauchyRecursionTasteGate_round_trip :
    ∀ x : RegularCauchyRecursionUp,
      regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S D E L H C P N =>
      change
        some
          (RegularCauchyRecursionUp.mk
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist Q))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist S))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist D))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist E))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist L))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist H))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist C))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist P))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist N))) =
          some (RegularCauchyRecursionUp.mk Q S D E L H C P N)
      exact congrArg some (RegularCauchyRecursionTasteGate_mk_congr
        (RegularCauchyRecursionTasteGate_decode_encode Q)
        (RegularCauchyRecursionTasteGate_decode_encode S)
        (RegularCauchyRecursionTasteGate_decode_encode D)
        (RegularCauchyRecursionTasteGate_decode_encode E)
        (RegularCauchyRecursionTasteGate_decode_encode L)
        (RegularCauchyRecursionTasteGate_decode_encode H)
        (RegularCauchyRecursionTasteGate_decode_encode C)
        (RegularCauchyRecursionTasteGate_decode_encode P)
        (RegularCauchyRecursionTasteGate_decode_encode N))

private theorem RegularCauchyRecursionTasteGate_toEventFlow_injective
    {x y : RegularCauchyRecursionUp} :
    regularCauchyRecursionToEventFlow x = regularCauchyRecursionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q S D E L H C P N =>
  cases y with
  | mk Q2 S2 D2 E2 L2 H2 C2 P2 N2 =>
  intro heq
  change
    [regularCauchyRecursionEncodeBHist Q, regularCauchyRecursionEncodeBHist S,
      regularCauchyRecursionEncodeBHist D, regularCauchyRecursionEncodeBHist E,
      regularCauchyRecursionEncodeBHist L, regularCauchyRecursionEncodeBHist H,
      regularCauchyRecursionEncodeBHist C, regularCauchyRecursionEncodeBHist P,
      regularCauchyRecursionEncodeBHist N] =
        [regularCauchyRecursionEncodeBHist Q2, regularCauchyRecursionEncodeBHist S2,
          regularCauchyRecursionEncodeBHist D2, regularCauchyRecursionEncodeBHist E2,
          regularCauchyRecursionEncodeBHist L2, regularCauchyRecursionEncodeBHist H2,
          regularCauchyRecursionEncodeBHist C2, regularCauchyRecursionEncodeBHist P2,
          regularCauchyRecursionEncodeBHist N2] at heq
  injection heq with hQ tQ
  injection tQ with hS tS
  injection tS with hD tD
  injection tD with hE tE
  injection tE with hL tL
  injection tL with hH tH
  injection tH with hC tC
  injection tC with hP tP
  injection tP with hN _
  have hQeq : Q = Q2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hQ
    rw [RegularCauchyRecursionTasteGate_decode_encode Q,
      RegularCauchyRecursionTasteGate_decode_encode Q2] at h
    exact h
  have hSeq : S = S2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hS
    rw [RegularCauchyRecursionTasteGate_decode_encode S,
      RegularCauchyRecursionTasteGate_decode_encode S2] at h
    exact h
  have hDeq : D = D2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hD
    rw [RegularCauchyRecursionTasteGate_decode_encode D,
      RegularCauchyRecursionTasteGate_decode_encode D2] at h
    exact h
  have hEeq : E = E2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hE
    rw [RegularCauchyRecursionTasteGate_decode_encode E,
      RegularCauchyRecursionTasteGate_decode_encode E2] at h
    exact h
  have hLeq : L = L2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hL
    rw [RegularCauchyRecursionTasteGate_decode_encode L,
      RegularCauchyRecursionTasteGate_decode_encode L2] at h
    exact h
  have hHeq : H = H2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hH
    rw [RegularCauchyRecursionTasteGate_decode_encode H,
      RegularCauchyRecursionTasteGate_decode_encode H2] at h
    exact h
  have hCeq : C = C2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hC
    rw [RegularCauchyRecursionTasteGate_decode_encode C,
      RegularCauchyRecursionTasteGate_decode_encode C2] at h
    exact h
  have hPeq : P = P2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hP
    rw [RegularCauchyRecursionTasteGate_decode_encode P,
      RegularCauchyRecursionTasteGate_decode_encode P2] at h
    exact h
  have hNeq : N = N2 := by
    have h := congrArg regularCauchyRecursionDecodeBHist hN
    rw [RegularCauchyRecursionTasteGate_decode_encode N,
      RegularCauchyRecursionTasteGate_decode_encode N2] at h
    exact h
  rw [hQeq, hSeq, hDeq, hEeq, hLeq, hHeq, hCeq, hPeq, hNeq]

instance regularCauchyRecursionBHistCarrier : BHistCarrier RegularCauchyRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRecursionToEventFlow
  fromEventFlow := regularCauchyRecursionFromEventFlow

instance regularCauchyRecursionChapterTasteGate : ChapterTasteGate RegularCauchyRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) = some x
    exact RegularCauchyRecursionTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyRecursionTasteGate_toEventFlow_injective heq)

theorem RegularCauchyRecursionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyRecursionUp,
        regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyRecursionUp,
        regularCauchyRecursionToEventFlow x = regularCauchyRecursionToEventFlow y → x = y) ∧
      regularCauchyRecursionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyRecursionTasteGate_decode_encode
  constructor
  · exact RegularCauchyRecursionTasteGate_round_trip
  constructor
  · intro x y heq
    exact RegularCauchyRecursionTasteGate_toEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularCauchyRecursionUp
