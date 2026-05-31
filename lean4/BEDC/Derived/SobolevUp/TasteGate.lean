import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevUp : Type where
  | mk (D M V L G H C P N : BHist) : SobolevUp

def sobolevEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevEncodeBHist h

def sobolevDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevDecodeBHist tail)

private theorem SobolevTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sobolevDecodeBHist (sobolevEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem sobolev_mk_congr
    {D D' M M' V V' L L' G G' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hM : M' = M) (hV : V' = V) (hL : L' = L)
    (hG : G' = G) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    SobolevUp.mk D' M' V' L' G' H' C' P' N' =
      SobolevUp.mk D M V L G H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hM
  cases hV
  cases hL
  cases hG
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def sobolevFields : SobolevUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevUp.mk D M V L G H C P N => [D, M, V, L, G, H, C, P, N]

def sobolevToEventFlow : SobolevUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map sobolevEncodeBHist (sobolevFields x)

def sobolevFromEventFlow : EventFlow → Option SobolevUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _D :: [] => none
  | _D :: _M :: [] => none
  | _D :: _M :: _V :: [] => none
  | _D :: _M :: _V :: _L :: [] => none
  | _D :: _M :: _V :: _L :: _G :: [] => none
  | _D :: _M :: _V :: _L :: _G :: _H :: [] => none
  | _D :: _M :: _V :: _L :: _G :: _H :: _C :: [] => none
  | _D :: _M :: _V :: _L :: _G :: _H :: _C :: _P :: [] => none
  | D :: M :: V :: L :: G :: H :: C :: P :: N :: [] =>
      some
        (SobolevUp.mk
          (sobolevDecodeBHist D)
          (sobolevDecodeBHist M)
          (sobolevDecodeBHist V)
          (sobolevDecodeBHist L)
          (sobolevDecodeBHist G)
          (sobolevDecodeBHist H)
          (sobolevDecodeBHist C)
          (sobolevDecodeBHist P)
          (sobolevDecodeBHist N))
  | _D :: _M :: _V :: _L :: _G :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem SobolevTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SobolevUp, sobolevFromEventFlow (sobolevToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M V L G H C P N =>
      exact
        congrArg some
          (sobolev_mk_congr
            (SobolevTasteGate_single_carrier_alignment_decode D)
            (SobolevTasteGate_single_carrier_alignment_decode M)
            (SobolevTasteGate_single_carrier_alignment_decode V)
            (SobolevTasteGate_single_carrier_alignment_decode L)
            (SobolevTasteGate_single_carrier_alignment_decode G)
            (SobolevTasteGate_single_carrier_alignment_decode H)
            (SobolevTasteGate_single_carrier_alignment_decode C)
            (SobolevTasteGate_single_carrier_alignment_decode P)
            (SobolevTasteGate_single_carrier_alignment_decode N))

private theorem SobolevTasteGate_single_carrier_alignment_injective
    {x y : SobolevUp} :
    sobolevToEventFlow x = sobolevToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevFromEventFlow (sobolevToEventFlow x) =
        sobolevFromEventFlow (sobolevToEventFlow y) :=
    congrArg sobolevFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans
      (SobolevTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SobolevTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance sobolevBHistCarrier : BHistCarrier SobolevUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevToEventFlow
  fromEventFlow := sobolevFromEventFlow

instance sobolevChapterTasteGate : ChapterTasteGate SobolevUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sobolevFromEventFlow (sobolevToEventFlow x) = some x
    exact SobolevTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SobolevTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SobolevUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevChapterTasteGate

theorem SobolevTasteGate_single_carrier_alignment :
    (∀ h : BHist, sobolevDecodeBHist (sobolevEncodeBHist h) = h) ∧
      (∀ x : SobolevUp, sobolevFromEventFlow (sobolevToEventFlow x) = some x) ∧
        (∀ x y : SobolevUp, sobolevToEventFlow x = sobolevToEventFlow y → x = y) ∧
          sobolevEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SobolevTasteGate_single_carrier_alignment_decode,
      SobolevTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SobolevTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.SobolevUp
