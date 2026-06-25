import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationDyadicBlockWitnessUp : Type where
  | mk (A D W M R E H C P N : BHist) : CauchyCondensationDyadicBlockWitnessUp
  deriving DecidableEq

def cauchyCondensationDyadicBlockWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationDyadicBlockWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationDyadicBlockWitnessEncodeBHist h

def cauchyCondensationDyadicBlockWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationDyadicBlockWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationDyadicBlockWitnessDecodeBHist tail)

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyCondensationDyadicBlockWitnessDecodeBHist
          (cauchyCondensationDyadicBlockWitnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_mk_congr
    {A A' D D' W W' M M' R R' E E' H H' C C' P P' N N' : BHist}
    (hA : A = A') (hD : D = D') (hW : W = W') (hM : M = M') (hR : R = R')
    (hE : E = E') (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    CauchyCondensationDyadicBlockWitnessUp.mk A D W M R E H C P N =
      CauchyCondensationDyadicBlockWitnessUp.mk A' D' W' M' R' E' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hD
  cases hW
  cases hM
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyCondensationDyadicBlockWitnessFields :
    CauchyCondensationDyadicBlockWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationDyadicBlockWitnessUp.mk A D W M R E H C P N =>
      [A, D, W, M, R, E, H, C, P, N]

def cauchyCondensationDyadicBlockWitnessToEventFlow :
    CauchyCondensationDyadicBlockWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCondensationDyadicBlockWitnessFields x).map
        cauchyCondensationDyadicBlockWitnessEncodeBHist

def cauchyCondensationDyadicBlockWitnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => cauchyCondensationDyadicBlockWitnessEventAt n rest
  | _, [] => []

def cauchyCondensationDyadicBlockWitnessFromEventFlow
    (ef : EventFlow) : Option CauchyCondensationDyadicBlockWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCondensationDyadicBlockWitnessUp.mk
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 0 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 1 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 2 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 3 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 4 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 5 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 6 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 7 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 8 ef))
      (cauchyCondensationDyadicBlockWitnessDecodeBHist
        (cauchyCondensationDyadicBlockWitnessEventAt 9 ef)))

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_round_trip :
    ∀ x : CauchyCondensationDyadicBlockWitnessUp,
      cauchyCondensationDyadicBlockWitnessFromEventFlow
          (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D W M R E H C P N =>
      change
        some
          (CauchyCondensationDyadicBlockWitnessUp.mk
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist A))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist D))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist W))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist M))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist R))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist E))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist H))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist C))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist P))
            (cauchyCondensationDyadicBlockWitnessDecodeBHist
              (cauchyCondensationDyadicBlockWitnessEncodeBHist N))) =
          some (CauchyCondensationDyadicBlockWitnessUp.mk A D W M R E H C P N)
      exact congrArg some (CauchyCondensationDyadicBlockWitnessTasteGate_mk_congr
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode A)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode D)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode W)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode M)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode R)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode E)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode H)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode C)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode P)
        (CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode N))

private theorem CauchyCondensationDyadicBlockWitnessTasteGate_toEventFlow_injective
    {x y : CauchyCondensationDyadicBlockWitnessUp} :
    cauchyCondensationDyadicBlockWitnessToEventFlow x =
        cauchyCondensationDyadicBlockWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A D W M R E H C P N =>
  cases y with
  | mk A2 D2 W2 M2 R2 E2 H2 C2 P2 N2 =>
  intro heq
  change
    [cauchyCondensationDyadicBlockWitnessEncodeBHist A,
      cauchyCondensationDyadicBlockWitnessEncodeBHist D,
      cauchyCondensationDyadicBlockWitnessEncodeBHist W,
      cauchyCondensationDyadicBlockWitnessEncodeBHist M,
      cauchyCondensationDyadicBlockWitnessEncodeBHist R,
      cauchyCondensationDyadicBlockWitnessEncodeBHist E,
      cauchyCondensationDyadicBlockWitnessEncodeBHist H,
      cauchyCondensationDyadicBlockWitnessEncodeBHist C,
      cauchyCondensationDyadicBlockWitnessEncodeBHist P,
      cauchyCondensationDyadicBlockWitnessEncodeBHist N] =
        [cauchyCondensationDyadicBlockWitnessEncodeBHist A2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist D2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist W2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist M2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist R2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist E2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist H2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist C2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist P2,
          cauchyCondensationDyadicBlockWitnessEncodeBHist N2] at heq
  injection heq with hA tA
  injection tA with hD tD
  injection tD with hW tW
  injection tW with hM tM
  injection tM with hR tR
  injection tR with hE tE
  injection tE with hH tH
  injection tH with hC tC
  injection tC with hP tP
  injection tP with hN _
  have hAeq : A = A2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hA
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode A,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode A2] at h
    exact h
  have hDeq : D = D2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hD
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode D,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode D2] at h
    exact h
  have hWeq : W = W2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hW
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode W,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode W2] at h
    exact h
  have hMeq : M = M2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hM
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode M,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode M2] at h
    exact h
  have hReq : R = R2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hR
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode R,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode R2] at h
    exact h
  have hEeq : E = E2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hE
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode E,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode E2] at h
    exact h
  have hHeq : H = H2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hH
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode H,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode H2] at h
    exact h
  have hCeq : C = C2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hC
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode C,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode C2] at h
    exact h
  have hPeq : P = P2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hP
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode P,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode P2] at h
    exact h
  have hNeq : N = N2 := by
    have h := congrArg cauchyCondensationDyadicBlockWitnessDecodeBHist hN
    rw [CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode N,
      CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode N2] at h
    exact h
  rw [hAeq, hDeq, hWeq, hMeq, hReq, hEeq, hHeq, hCeq, hPeq, hNeq]

instance cauchyCondensationDyadicBlockWitnessBHistCarrier :
    BHistCarrier CauchyCondensationDyadicBlockWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationDyadicBlockWitnessToEventFlow
  fromEventFlow := cauchyCondensationDyadicBlockWitnessFromEventFlow

instance cauchyCondensationDyadicBlockWitnessChapterTasteGate :
    ChapterTasteGate CauchyCondensationDyadicBlockWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCondensationDyadicBlockWitnessFromEventFlow
          (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
        some x
    exact CauchyCondensationDyadicBlockWitnessTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCondensationDyadicBlockWitnessTasteGate_toEventFlow_injective heq)

theorem CauchyCondensationDyadicBlockWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCondensationDyadicBlockWitnessDecodeBHist
          (cauchyCondensationDyadicBlockWitnessEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCondensationDyadicBlockWitnessUp,
        cauchyCondensationDyadicBlockWitnessFromEventFlow
            (cauchyCondensationDyadicBlockWitnessToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCondensationDyadicBlockWitnessUp,
        cauchyCondensationDyadicBlockWitnessToEventFlow x =
            cauchyCondensationDyadicBlockWitnessToEventFlow y →
          x = y) ∧
      cauchyCondensationDyadicBlockWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCondensationDyadicBlockWitnessTasteGate_decode_encode
  constructor
  · exact CauchyCondensationDyadicBlockWitnessTasteGate_round_trip
  constructor
  · intro x y heq
    exact CauchyCondensationDyadicBlockWitnessTasteGate_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp
