import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICBetaAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICBetaAuditUp : Type where
  | mk (S V T F O H C P N : BHist) : MetaCICBetaAuditUp

def metaCICBetaAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICBetaAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICBetaAuditEncodeBHist h

def metaCICBetaAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICBetaAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICBetaAuditDecodeBHist tail)

private theorem MetaCICBetaAuditTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metaCICBetaAuditDecodeBHist
        (metaCICBetaAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metaCICBetaAudit_mk_congr
    {S S' V V' T T' F F' O O' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hV : V' = V) (hT : T' = T) (hF : F' = F) (hO : O' = O)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    MetaCICBetaAuditUp.mk S' V' T' F' O' H' C' P' N' =
      MetaCICBetaAuditUp.mk S V T F O H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hV
  cases hT
  cases hF
  cases hO
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def metaCICBetaAuditFields : MetaCICBetaAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICBetaAuditUp.mk S V T F O H C P N => [S, V, T, F, O, H, C, P, N]

def metaCICBetaAuditToEventFlow : MetaCICBetaAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map metaCICBetaAuditEncodeBHist (metaCICBetaAuditFields x)

def metaCICBetaAuditFromEventFlow :
    EventFlow → Option MetaCICBetaAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _S :: [] => none
  | _S :: _V :: [] => none
  | _S :: _V :: _T :: [] => none
  | _S :: _V :: _T :: _F :: [] => none
  | _S :: _V :: _T :: _F :: _O :: [] => none
  | _S :: _V :: _T :: _F :: _O :: _H :: [] => none
  | _S :: _V :: _T :: _F :: _O :: _H :: _C :: [] => none
  | _S :: _V :: _T :: _F :: _O :: _H :: _C :: _P :: [] => none
  | S :: V :: T :: F :: O :: H :: C :: P :: N :: [] =>
      some
        (MetaCICBetaAuditUp.mk
          (metaCICBetaAuditDecodeBHist S)
          (metaCICBetaAuditDecodeBHist V)
          (metaCICBetaAuditDecodeBHist T)
          (metaCICBetaAuditDecodeBHist F)
          (metaCICBetaAuditDecodeBHist O)
          (metaCICBetaAuditDecodeBHist H)
          (metaCICBetaAuditDecodeBHist C)
          (metaCICBetaAuditDecodeBHist P)
          (metaCICBetaAuditDecodeBHist N))
  | _S :: _V :: _T :: _F :: _O :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem MetaCICBetaAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICBetaAuditUp,
      metaCICBetaAuditFromEventFlow
        (metaCICBetaAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S V T F O H C P N =>
      exact
        congrArg some
          (metaCICBetaAudit_mk_congr
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode S)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode V)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode T)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode F)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode O)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode H)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode C)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode P)
            (MetaCICBetaAuditTasteGate_single_carrier_alignment_decode N))

private theorem MetaCICBetaAuditTasteGate_single_carrier_alignment_injective
    {x y : MetaCICBetaAuditUp} :
    metaCICBetaAuditToEventFlow x = metaCICBetaAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICBetaAuditFromEventFlow
          (metaCICBetaAuditToEventFlow x) =
        metaCICBetaAuditFromEventFlow
          (metaCICBetaAuditToEventFlow y) :=
    congrArg metaCICBetaAuditFromEventFlow heq
  have hsome :
      some x = some y :=
    Eq.trans
      (MetaCICBetaAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICBetaAuditTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance metaCICBetaAuditBHistCarrier :
    BHistCarrier MetaCICBetaAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICBetaAuditToEventFlow
  fromEventFlow := metaCICBetaAuditFromEventFlow

instance metaCICBetaAuditChapterTasteGate :
    ChapterTasteGate MetaCICBetaAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICBetaAuditFromEventFlow
        (metaCICBetaAuditToEventFlow x) = some x
    exact MetaCICBetaAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICBetaAuditTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate MetaCICBetaAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICBetaAuditChapterTasteGate

theorem MetaCICBetaAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICBetaAuditDecodeBHist (metaCICBetaAuditEncodeBHist h) = h) ∧
      (∀ x : MetaCICBetaAuditUp,
        metaCICBetaAuditFromEventFlow (metaCICBetaAuditToEventFlow x) = some x) ∧
        (∀ x y : MetaCICBetaAuditUp,
          metaCICBetaAuditToEventFlow x = metaCICBetaAuditToEventFlow y → x = y) ∧
          metaCICBetaAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICBetaAuditTasteGate_single_carrier_alignment_decode,
      MetaCICBetaAuditTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MetaCICBetaAuditTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICBetaAuditUp
