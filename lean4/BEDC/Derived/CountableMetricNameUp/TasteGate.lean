import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableMetricNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableMetricNameUp : Type where
  | mk (S M W D R E H C P N : BHist) : CountableMetricNameUp
  deriving DecidableEq

def countableMetricNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableMetricNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countableMetricNameEncodeBHist h

def countableMetricNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableMetricNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countableMetricNameDecodeBHist tail)

private theorem CountableMetricNameTasteGate_decode_encode :
    ∀ h : BHist, countableMetricNameDecodeBHist (countableMetricNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CountableMetricNameTasteGate_mk_congr
    {S S' M M' W W' D D' R R' E E' H H' C C' P P' N N' : BHist}
    (hS : S = S') (hM : M = M') (hW : W = W') (hD : D = D') (hR : R = R')
    (hE : E = E') (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    CountableMetricNameUp.mk S M W D R E H C P N =
      CountableMetricNameUp.mk S' M' W' D' R' E' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def countableMetricNameFields : CountableMetricNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountableMetricNameUp.mk S M W D R E H C P N => [S, M, W, D, R, E, H, C, P, N]

def countableMetricNameToEventFlow : CountableMetricNameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (countableMetricNameFields x).map countableMetricNameEncodeBHist

def countableMetricNameEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => countableMetricNameEventAt n rest
  | _, [] => []

def countableMetricNameFromEventFlow (ef : EventFlow) : Option CountableMetricNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CountableMetricNameUp.mk
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 0 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 1 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 2 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 3 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 4 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 5 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 6 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 7 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 8 ef))
      (countableMetricNameDecodeBHist (countableMetricNameEventAt 9 ef)))

private theorem CountableMetricNameTasteGate_round_trip :
    ∀ x : CountableMetricNameUp,
      countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W D R E H C P N =>
      change
        some
          (CountableMetricNameUp.mk
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist S))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist M))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist W))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist D))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist R))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist E))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist H))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist C))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist P))
            (countableMetricNameDecodeBHist (countableMetricNameEncodeBHist N))) =
          some (CountableMetricNameUp.mk S M W D R E H C P N)
      exact congrArg some (CountableMetricNameTasteGate_mk_congr
        (CountableMetricNameTasteGate_decode_encode S)
        (CountableMetricNameTasteGate_decode_encode M)
        (CountableMetricNameTasteGate_decode_encode W)
        (CountableMetricNameTasteGate_decode_encode D)
        (CountableMetricNameTasteGate_decode_encode R)
        (CountableMetricNameTasteGate_decode_encode E)
        (CountableMetricNameTasteGate_decode_encode H)
        (CountableMetricNameTasteGate_decode_encode C)
        (CountableMetricNameTasteGate_decode_encode P)
        (CountableMetricNameTasteGate_decode_encode N))

private theorem CountableMetricNameTasteGate_toEventFlow_injective {x y : CountableMetricNameUp} :
    countableMetricNameToEventFlow x = countableMetricNameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M W D R E H C P N =>
  cases y with
  | mk S2 M2 W2 D2 R2 E2 H2 C2 P2 N2 =>
  intro heq
  change
    [countableMetricNameEncodeBHist S, countableMetricNameEncodeBHist M,
      countableMetricNameEncodeBHist W, countableMetricNameEncodeBHist D,
      countableMetricNameEncodeBHist R, countableMetricNameEncodeBHist E,
      countableMetricNameEncodeBHist H, countableMetricNameEncodeBHist C,
      countableMetricNameEncodeBHist P, countableMetricNameEncodeBHist N] =
        [countableMetricNameEncodeBHist S2, countableMetricNameEncodeBHist M2,
          countableMetricNameEncodeBHist W2, countableMetricNameEncodeBHist D2,
          countableMetricNameEncodeBHist R2, countableMetricNameEncodeBHist E2,
          countableMetricNameEncodeBHist H2, countableMetricNameEncodeBHist C2,
          countableMetricNameEncodeBHist P2, countableMetricNameEncodeBHist N2] at heq
  injection heq with hS tS
  injection tS with hM tM
  injection tM with hW tW
  injection tW with hD tD
  injection tD with hR tR
  injection tR with hE tE
  injection tE with hH tH
  injection tH with hC tC
  injection tC with hP tP
  injection tP with hN _
  have hSeq : S = S2 := by
    have h := congrArg countableMetricNameDecodeBHist hS
    rw [CountableMetricNameTasteGate_decode_encode S,
      CountableMetricNameTasteGate_decode_encode S2] at h
    exact h
  have hMeq : M = M2 := by
    have h := congrArg countableMetricNameDecodeBHist hM
    rw [CountableMetricNameTasteGate_decode_encode M,
      CountableMetricNameTasteGate_decode_encode M2] at h
    exact h
  have hWeq : W = W2 := by
    have h := congrArg countableMetricNameDecodeBHist hW
    rw [CountableMetricNameTasteGate_decode_encode W,
      CountableMetricNameTasteGate_decode_encode W2] at h
    exact h
  have hDeq : D = D2 := by
    have h := congrArg countableMetricNameDecodeBHist hD
    rw [CountableMetricNameTasteGate_decode_encode D,
      CountableMetricNameTasteGate_decode_encode D2] at h
    exact h
  have hReq : R = R2 := by
    have h := congrArg countableMetricNameDecodeBHist hR
    rw [CountableMetricNameTasteGate_decode_encode R,
      CountableMetricNameTasteGate_decode_encode R2] at h
    exact h
  have hEeq : E = E2 := by
    have h := congrArg countableMetricNameDecodeBHist hE
    rw [CountableMetricNameTasteGate_decode_encode E,
      CountableMetricNameTasteGate_decode_encode E2] at h
    exact h
  have hHeq : H = H2 := by
    have h := congrArg countableMetricNameDecodeBHist hH
    rw [CountableMetricNameTasteGate_decode_encode H,
      CountableMetricNameTasteGate_decode_encode H2] at h
    exact h
  have hCeq : C = C2 := by
    have h := congrArg countableMetricNameDecodeBHist hC
    rw [CountableMetricNameTasteGate_decode_encode C,
      CountableMetricNameTasteGate_decode_encode C2] at h
    exact h
  have hPeq : P = P2 := by
    have h := congrArg countableMetricNameDecodeBHist hP
    rw [CountableMetricNameTasteGate_decode_encode P,
      CountableMetricNameTasteGate_decode_encode P2] at h
    exact h
  have hNeq : N = N2 := by
    have h := congrArg countableMetricNameDecodeBHist hN
    rw [CountableMetricNameTasteGate_decode_encode N,
      CountableMetricNameTasteGate_decode_encode N2] at h
    exact h
  rw [hSeq, hMeq, hWeq, hDeq, hReq, hEeq, hHeq, hCeq, hPeq, hNeq]

instance countableMetricNameBHistCarrier : BHistCarrier CountableMetricNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableMetricNameToEventFlow
  fromEventFlow := countableMetricNameFromEventFlow

instance countableMetricNameChapterTasteGate : ChapterTasteGate CountableMetricNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) = some x
    exact CountableMetricNameTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CountableMetricNameTasteGate_toEventFlow_injective heq)

theorem CountableMetricNameTasteGate_single_carrier_alignment :
    (∀ h : BHist, countableMetricNameDecodeBHist (countableMetricNameEncodeBHist h) = h) ∧
      (∀ x : CountableMetricNameUp,
        countableMetricNameFromEventFlow (countableMetricNameToEventFlow x) = some x) ∧
      (∀ x y : CountableMetricNameUp,
        countableMetricNameToEventFlow x = countableMetricNameToEventFlow y → x = y) ∧
      countableMetricNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CountableMetricNameTasteGate_decode_encode
  constructor
  · exact CountableMetricNameTasteGate_round_trip
  constructor
  · intro x y heq
    exact CountableMetricNameTasteGate_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CountableMetricNameUp
