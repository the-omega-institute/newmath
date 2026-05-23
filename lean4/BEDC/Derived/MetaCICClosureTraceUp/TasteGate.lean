import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICClosureTraceUp : Type where
  | mk (S U V B R G K H C P N : BHist) : MetaCICClosureTraceUp

def metaCICClosureTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICClosureTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICClosureTraceEncodeBHist h

def metaCICClosureTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICClosureTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICClosureTraceDecodeBHist tail)

private theorem MetaCICClosureTraceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metaCICClosureTraceDecodeBHist
        (metaCICClosureTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metaCICClosureTrace_mk_congr
    {S S' U U' V V' B B' R R' G G' K K' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hU : U' = U) (hV : V' = V) (hB : B' = B) (hR : R' = R)
    (hG : G' = G) (hK : K' = K) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    MetaCICClosureTraceUp.mk S' U' V' B' R' G' K' H' C' P' N' =
      MetaCICClosureTraceUp.mk S U V B R G K H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hU
  cases hV
  cases hB
  cases hR
  cases hG
  cases hK
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def metaCICClosureTraceFields : MetaCICClosureTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICClosureTraceUp.mk S U V B R G K H C P N => [S, U, V, B, R, G, K, H, C, P, N]

def metaCICClosureTraceToEventFlow : MetaCICClosureTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map metaCICClosureTraceEncodeBHist (metaCICClosureTraceFields x)

def metaCICClosureTraceFromEventFlow :
    EventFlow → Option MetaCICClosureTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _S :: [] => none
  | _S :: _U :: [] => none
  | _S :: _U :: _V :: [] => none
  | _S :: _U :: _V :: _B :: [] => none
  | _S :: _U :: _V :: _B :: _R :: [] => none
  | _S :: _U :: _V :: _B :: _R :: _G :: [] => none
  | _S :: _U :: _V :: _B :: _R :: _G :: _K :: [] => none
  | _S :: _U :: _V :: _B :: _R :: _G :: _K :: _H :: [] => none
  | _S :: _U :: _V :: _B :: _R :: _G :: _K :: _H :: _C :: [] => none
  | _S :: _U :: _V :: _B :: _R :: _G :: _K :: _H :: _C :: _P :: [] => none
  | S :: U :: V :: B :: R :: G :: K :: H :: C :: P :: N :: [] =>
      some
        (MetaCICClosureTraceUp.mk
          (metaCICClosureTraceDecodeBHist S)
          (metaCICClosureTraceDecodeBHist U)
          (metaCICClosureTraceDecodeBHist V)
          (metaCICClosureTraceDecodeBHist B)
          (metaCICClosureTraceDecodeBHist R)
          (metaCICClosureTraceDecodeBHist G)
          (metaCICClosureTraceDecodeBHist K)
          (metaCICClosureTraceDecodeBHist H)
          (metaCICClosureTraceDecodeBHist C)
          (metaCICClosureTraceDecodeBHist P)
          (metaCICClosureTraceDecodeBHist N))
  | _S :: _U :: _V :: _B :: _R :: _G :: _K :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem MetaCICClosureTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICClosureTraceUp,
      metaCICClosureTraceFromEventFlow
        (metaCICClosureTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U V B R G K H C P N =>
      exact
        congrArg some
          (metaCICClosureTrace_mk_congr
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode S)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode U)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode V)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode B)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode R)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode G)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode K)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode H)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode C)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode P)
            (MetaCICClosureTraceTasteGate_single_carrier_alignment_decode N))

private theorem MetaCICClosureTraceTasteGate_single_carrier_alignment_injective
    {x y : MetaCICClosureTraceUp} :
    metaCICClosureTraceToEventFlow x = metaCICClosureTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICClosureTraceFromEventFlow
          (metaCICClosureTraceToEventFlow x) =
        metaCICClosureTraceFromEventFlow
          (metaCICClosureTraceToEventFlow y) :=
    congrArg metaCICClosureTraceFromEventFlow heq
  have hsome :
      some x = some y :=
    Eq.trans
      (MetaCICClosureTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICClosureTraceTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance metaCICClosureTraceBHistCarrier :
    BHistCarrier MetaCICClosureTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICClosureTraceToEventFlow
  fromEventFlow := metaCICClosureTraceFromEventFlow

instance metaCICClosureTraceChapterTasteGate :
    ChapterTasteGate MetaCICClosureTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICClosureTraceFromEventFlow
        (metaCICClosureTraceToEventFlow x) = some x
    exact MetaCICClosureTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICClosureTraceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate MetaCICClosureTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICClosureTraceChapterTasteGate

theorem MetaCICClosureTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICClosureTraceDecodeBHist (metaCICClosureTraceEncodeBHist h) = h) ∧
      (∀ x : MetaCICClosureTraceUp,
        metaCICClosureTraceFromEventFlow (metaCICClosureTraceToEventFlow x) = some x) ∧
        (∀ x y : MetaCICClosureTraceUp,
          metaCICClosureTraceToEventFlow x = metaCICClosureTraceToEventFlow y → x = y) ∧
          metaCICClosureTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICClosureTraceTasteGate_single_carrier_alignment_decode,
      MetaCICClosureTraceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MetaCICClosureTraceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICClosureTraceUp
