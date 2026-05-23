import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICSubjectReductionObligationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICSubjectReductionObligationUp : Type where
  | mk (B A L P Q R H C G N : BHist) : MetaCICSubjectReductionObligationUp

def metaCICSubjectReductionObligationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICSubjectReductionObligationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICSubjectReductionObligationEncodeBHist h

def metaCICSubjectReductionObligationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICSubjectReductionObligationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICSubjectReductionObligationDecodeBHist tail)

private theorem MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metaCICSubjectReductionObligationDecodeBHist
        (metaCICSubjectReductionObligationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metaCICSubjectReductionObligation_mk_congr
    {B B' A A' L L' P P' Q Q' R R' H H' C C' G G' N N' : BHist}
    (hB : B' = B) (hA : A' = A) (hL : L' = L) (hP : P' = P) (hQ : Q' = Q)
    (hR : R' = R) (hH : H' = H) (hC : C' = C) (hG : G' = G) (hN : N' = N) :
    MetaCICSubjectReductionObligationUp.mk B' A' L' P' Q' R' H' C' G' N' =
      MetaCICSubjectReductionObligationUp.mk B A L P Q R H C G N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hA
  cases hL
  cases hP
  cases hQ
  cases hR
  cases hH
  cases hC
  cases hG
  cases hN
  rfl

def metaCICSubjectReductionObligationFields :
    MetaCICSubjectReductionObligationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICSubjectReductionObligationUp.mk B A L P Q R H C G N =>
      [B, A, L, P, Q, R, H, C, G, N]

def metaCICSubjectReductionObligationToEventFlow :
    MetaCICSubjectReductionObligationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map metaCICSubjectReductionObligationEncodeBHist
        (metaCICSubjectReductionObligationFields x)

def metaCICSubjectReductionObligationFromEventFlow :
    EventFlow → Option MetaCICSubjectReductionObligationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _B :: [] => none
  | _B :: _A :: [] => none
  | _B :: _A :: _L :: [] => none
  | _B :: _A :: _L :: _P :: [] => none
  | _B :: _A :: _L :: _P :: _Q :: [] => none
  | _B :: _A :: _L :: _P :: _Q :: _R :: [] => none
  | _B :: _A :: _L :: _P :: _Q :: _R :: _H :: [] => none
  | _B :: _A :: _L :: _P :: _Q :: _R :: _H :: _C :: [] => none
  | _B :: _A :: _L :: _P :: _Q :: _R :: _H :: _C :: _G :: [] => none
  | B :: A :: L :: P :: Q :: R :: H :: C :: G :: N :: [] =>
      some
        (MetaCICSubjectReductionObligationUp.mk
          (metaCICSubjectReductionObligationDecodeBHist B)
          (metaCICSubjectReductionObligationDecodeBHist A)
          (metaCICSubjectReductionObligationDecodeBHist L)
          (metaCICSubjectReductionObligationDecodeBHist P)
          (metaCICSubjectReductionObligationDecodeBHist Q)
          (metaCICSubjectReductionObligationDecodeBHist R)
          (metaCICSubjectReductionObligationDecodeBHist H)
          (metaCICSubjectReductionObligationDecodeBHist C)
          (metaCICSubjectReductionObligationDecodeBHist G)
          (metaCICSubjectReductionObligationDecodeBHist N))
  | _B :: _A :: _L :: _P :: _Q :: _R :: _H :: _C :: _G :: _N :: _extra :: _rest =>
      none

private theorem MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICSubjectReductionObligationUp,
      metaCICSubjectReductionObligationFromEventFlow
        (metaCICSubjectReductionObligationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A L P Q R H C G N =>
      exact
        congrArg some
          (metaCICSubjectReductionObligation_mk_congr
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode B)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode A)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode L)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode P)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode Q)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode R)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode H)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode C)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode G)
            (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode N))

private theorem MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_injective
    {x y : MetaCICSubjectReductionObligationUp} :
    metaCICSubjectReductionObligationToEventFlow x =
      metaCICSubjectReductionObligationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICSubjectReductionObligationFromEventFlow
          (metaCICSubjectReductionObligationToEventFlow x) =
        metaCICSubjectReductionObligationFromEventFlow
          (metaCICSubjectReductionObligationToEventFlow y) :=
    congrArg metaCICSubjectReductionObligationFromEventFlow heq
  have hsome :
      some x = some y :=
    Eq.trans
      (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance metaCICSubjectReductionObligationBHistCarrier :
    BHistCarrier MetaCICSubjectReductionObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICSubjectReductionObligationToEventFlow
  fromEventFlow := metaCICSubjectReductionObligationFromEventFlow

instance metaCICSubjectReductionObligationChapterTasteGate :
    ChapterTasteGate MetaCICSubjectReductionObligationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICSubjectReductionObligationFromEventFlow
        (metaCICSubjectReductionObligationToEventFlow x) = some x
    exact MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate MetaCICSubjectReductionObligationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICSubjectReductionObligationChapterTasteGate

theorem MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICSubjectReductionObligationDecodeBHist
        (metaCICSubjectReductionObligationEncodeBHist h) = h) ∧
      (∀ x : MetaCICSubjectReductionObligationUp,
        metaCICSubjectReductionObligationFromEventFlow
          (metaCICSubjectReductionObligationToEventFlow x) = some x) ∧
        (∀ x y : MetaCICSubjectReductionObligationUp,
          metaCICSubjectReductionObligationToEventFlow x =
            metaCICSubjectReductionObligationToEventFlow y → x = y) ∧
          metaCICSubjectReductionObligationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_decode,
      MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICSubjectReductionObligationTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICSubjectReductionObligationUp
