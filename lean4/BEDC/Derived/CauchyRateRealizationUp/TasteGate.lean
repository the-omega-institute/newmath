import BEDC.Derived.CauchyRateRealizationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateRealizationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived

def cauchyRateRealizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateRealizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateRealizationEncodeBHist h

def cauchyRateRealizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateRealizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateRealizationDecodeBHist tail)

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateRealizationFields : CauchyRateRealizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateRealizationUp.mk p r d s q m e H C P N =>
      [p, r, d, s, q, m, e, H, C, P, N]

def cauchyRateRealizationToEventFlow : CauchyRateRealizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRateRealizationFields x).map cauchyRateRealizationEncodeBHist

def cauchyRateRealizationFromEventFlow : EventFlow → Option CauchyRateRealizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | p :: r :: d :: s :: q :: m :: e :: H :: C :: P :: N :: [] =>
      some
        (CauchyRateRealizationUp.mk
          (cauchyRateRealizationDecodeBHist p)
          (cauchyRateRealizationDecodeBHist r)
          (cauchyRateRealizationDecodeBHist d)
          (cauchyRateRealizationDecodeBHist s)
          (cauchyRateRealizationDecodeBHist q)
          (cauchyRateRealizationDecodeBHist m)
          (cauchyRateRealizationDecodeBHist e)
          (cauchyRateRealizationDecodeBHist H)
          (cauchyRateRealizationDecodeBHist C)
          (cauchyRateRealizationDecodeBHist P)
          (cauchyRateRealizationDecodeBHist N))
  | _ => none

private theorem cauchyRateRealization_round_trip :
    ∀ x : CauchyRateRealizationUp,
      cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p r d s q m e H C P N =>
      change
        some
          (CauchyRateRealizationUp.mk
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist p))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist r))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist d))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist s))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist q))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist m))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist e))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist H))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist C))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist P))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist N))) =
          some (CauchyRateRealizationUp.mk p r d s q m e H C P N)
      rw [CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode p,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode r,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode d,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode s,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode q,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode m,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode e,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem cauchyRateRealizationToEventFlow_injective {x y : CauchyRateRealizationUp} :
    cauchyRateRealizationToEventFlow x = cauchyRateRealizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) =
        cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow y) :=
    congrArg cauchyRateRealizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRateRealization_round_trip x).symm
      (Eq.trans hread (cauchyRateRealization_round_trip y)))

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    cauchyRateRealizationEncodeBHist h = cauchyRateRealizationEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  calc
    h = cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist h) :=
      (CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode h).symm
    _ = cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist k) :=
      congrArg cauchyRateRealizationDecodeBHist heq
    _ = k := CauchyRateRealizationTasteGate_single_carrier_alignment_decode_encode k

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_direct
    {x y : CauchyRateRealizationUp} :
    cauchyRateRealizationToEventFlow x = cauchyRateRealizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk p₁ r₁ d₁ s₁ q₁ m₁ e₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk p₂ r₂ d₂ s₂ q₂ m₂ e₂ H₂ C₂ P₂ N₂ =>
          change
            [cauchyRateRealizationEncodeBHist p₁, cauchyRateRealizationEncodeBHist r₁,
              cauchyRateRealizationEncodeBHist d₁, cauchyRateRealizationEncodeBHist s₁,
              cauchyRateRealizationEncodeBHist q₁, cauchyRateRealizationEncodeBHist m₁,
              cauchyRateRealizationEncodeBHist e₁, cauchyRateRealizationEncodeBHist H₁,
              cauchyRateRealizationEncodeBHist C₁, cauchyRateRealizationEncodeBHist P₁,
              cauchyRateRealizationEncodeBHist N₁] =
              [cauchyRateRealizationEncodeBHist p₂, cauchyRateRealizationEncodeBHist r₂,
                cauchyRateRealizationEncodeBHist d₂, cauchyRateRealizationEncodeBHist s₂,
                cauchyRateRealizationEncodeBHist q₂, cauchyRateRealizationEncodeBHist m₂,
                cauchyRateRealizationEncodeBHist e₂, cauchyRateRealizationEncodeBHist H₂,
                cauchyRateRealizationEncodeBHist C₂, cauchyRateRealizationEncodeBHist P₂,
                cauchyRateRealizationEncodeBHist N₂] at heq
          injection heq with hp tail0
          injection tail0 with hr tail1
          injection tail1 with hd tail2
          injection tail2 with hs tail3
          injection tail3 with hq tail4
          injection tail4 with hm tail5
          injection tail5 with he tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          have hpEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hp
          have hrEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hr
          have hdEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hd
          have hsEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hs
          have hqEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hq
          have hmEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hm
          have heEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective he
          have hHEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hH
          have hCEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hC
          have hPEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hP
          have hNEq :=
            CauchyRateRealizationTasteGate_single_carrier_alignment_encode_injective hN
          subst hpEq
          subst hrEq
          subst hdEq
          subst hsEq
          subst hqEq
          subst hmEq
          subst heEq
          subst hHEq
          subst hCEq
          subst hPEq
          subst hNEq
          rfl

instance cauchyRateRealizationBHistCarrier :
    BHistCarrier CauchyRateRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateRealizationToEventFlow
  fromEventFlow := cauchyRateRealizationFromEventFlow

instance cauchyRateRealizationChapterTasteGate :
    ChapterTasteGate CauchyRateRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) = some x
    exact cauchyRateRealization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRateRealizationToEventFlow_injective heq)

theorem CauchyRateRealizationTasteGate_single_carrier_alignment
    (x y : CauchyRateRealizationUp) :
    cauchyRateRealizationToEventFlow x = cauchyRateRealizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact CauchyRateRealizationTasteGate_single_carrier_alignment_direct

end BEDC.Derived.CauchyRateRealizationUp.TasteGate
