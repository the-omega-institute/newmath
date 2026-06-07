import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorSpaceCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorSpaceCompactnessUp : Type where
  | mk : (C F T S B H R Q P N : BHist) → CantorSpaceCompactnessUp
  deriving DecidableEq

def cantorSpaceCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorSpaceCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorSpaceCompactnessEncodeBHist h

def cantorSpaceCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorSpaceCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorSpaceCompactnessDecodeBHist tail)

private theorem cantorSpaceCompactnessDecode_encode_bhist :
    ∀ h : BHist,
      cantorSpaceCompactnessDecodeBHist (cantorSpaceCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cantorSpaceCompactness_mk_congr
    {C C' F F' T T' S S' B B' H H' R R' Q Q' P P' N N' : BHist}
    (hC : C' = C) (hF : F' = F) (hT : T' = T) (hS : S' = S) (hB : B' = B)
    (hH : H' = H) (hR : R' = R) (hQ : Q' = Q) (hP : P' = P) (hN : N' = N) :
    CantorSpaceCompactnessUp.mk C' F' T' S' B' H' R' Q' P' N' =
      CantorSpaceCompactnessUp.mk C F T S B H R Q P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hF
  cases hT
  cases hS
  cases hB
  cases hH
  cases hR
  cases hQ
  cases hP
  cases hN
  rfl

def cantorSpaceCompactnessFields :
    CantorSpaceCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorSpaceCompactnessUp.mk C F T S B H R Q P N => [C, F, T, S, B, H, R, Q, P, N]

def cantorSpaceCompactnessToEventFlow :
    CantorSpaceCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cantorSpaceCompactnessFields x).map cantorSpaceCompactnessEncodeBHist

def cantorSpaceCompactnessFromEventFlow :
    EventFlow → Option CantorSpaceCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _C :: [] => none
  | _C :: _F :: [] => none
  | _C :: _F :: _T :: [] => none
  | _C :: _F :: _T :: _S :: [] => none
  | _C :: _F :: _T :: _S :: _B :: [] => none
  | _C :: _F :: _T :: _S :: _B :: _H :: [] => none
  | _C :: _F :: _T :: _S :: _B :: _H :: _R :: [] => none
  | _C :: _F :: _T :: _S :: _B :: _H :: _R :: _Q :: [] => none
  | _C :: _F :: _T :: _S :: _B :: _H :: _R :: _Q :: _P :: [] => none
  | C :: F :: T :: S :: B :: H :: R :: Q :: P :: N :: [] =>
      some
        (CantorSpaceCompactnessUp.mk
          (cantorSpaceCompactnessDecodeBHist C)
          (cantorSpaceCompactnessDecodeBHist F)
          (cantorSpaceCompactnessDecodeBHist T)
          (cantorSpaceCompactnessDecodeBHist S)
          (cantorSpaceCompactnessDecodeBHist B)
          (cantorSpaceCompactnessDecodeBHist H)
          (cantorSpaceCompactnessDecodeBHist R)
          (cantorSpaceCompactnessDecodeBHist Q)
          (cantorSpaceCompactnessDecodeBHist P)
          (cantorSpaceCompactnessDecodeBHist N))
  | _C :: _F :: _T :: _S :: _B :: _H :: _R :: _Q :: _P :: _N :: _extra :: _rest =>
      none

private theorem cantorSpaceCompactness_round_trip :
    ∀ x : CantorSpaceCompactnessUp,
      cantorSpaceCompactnessFromEventFlow (cantorSpaceCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C F T S B H R Q P N =>
      exact
        congrArg some
          (cantorSpaceCompactness_mk_congr
            (cantorSpaceCompactnessDecode_encode_bhist C)
            (cantorSpaceCompactnessDecode_encode_bhist F)
            (cantorSpaceCompactnessDecode_encode_bhist T)
            (cantorSpaceCompactnessDecode_encode_bhist S)
            (cantorSpaceCompactnessDecode_encode_bhist B)
            (cantorSpaceCompactnessDecode_encode_bhist H)
            (cantorSpaceCompactnessDecode_encode_bhist R)
            (cantorSpaceCompactnessDecode_encode_bhist Q)
            (cantorSpaceCompactnessDecode_encode_bhist P)
            (cantorSpaceCompactnessDecode_encode_bhist N))

private theorem cantorSpaceCompactnessToEventFlow_injective
    {x y : CantorSpaceCompactnessUp} :
    cantorSpaceCompactnessToEventFlow x = cantorSpaceCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorSpaceCompactnessFromEventFlow (cantorSpaceCompactnessToEventFlow x) =
        cantorSpaceCompactnessFromEventFlow (cantorSpaceCompactnessToEventFlow y) :=
    congrArg cantorSpaceCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cantorSpaceCompactness_round_trip x).symm
      (Eq.trans hread (cantorSpaceCompactness_round_trip y)))

instance cantorSpaceCompactnessBHistCarrier : BHistCarrier CantorSpaceCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorSpaceCompactnessToEventFlow
  fromEventFlow := cantorSpaceCompactnessFromEventFlow

instance cantorSpaceCompactnessChapterTasteGate :
    ChapterTasteGate CantorSpaceCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorSpaceCompactnessFromEventFlow (cantorSpaceCompactnessToEventFlow x) =
      some x
    exact cantorSpaceCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorSpaceCompactnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CantorSpaceCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorSpaceCompactnessChapterTasteGate

theorem CantorSpaceCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cantorSpaceCompactnessDecodeBHist (cantorSpaceCompactnessEncodeBHist h) = h) ∧
      (∀ x : CantorSpaceCompactnessUp,
        cantorSpaceCompactnessFromEventFlow (cantorSpaceCompactnessToEventFlow x) = some x) ∧
        (∀ x y : CantorSpaceCompactnessUp,
          cantorSpaceCompactnessToEventFlow x = cantorSpaceCompactnessToEventFlow y →
            x = y) ∧
          cantorSpaceCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cantorSpaceCompactnessDecode_encode_bhist,
      cantorSpaceCompactness_round_trip,
      (fun _ _ heq => cantorSpaceCompactnessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CantorSpaceCompactnessUp
