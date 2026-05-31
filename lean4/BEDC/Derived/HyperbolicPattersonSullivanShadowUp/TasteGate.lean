import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicPattersonSullivanShadowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicPattersonSullivanShadowUp : Type where
  | mk
      (boundaryBasepoint visualMetric shadowWindow countingBudget busemannTransport
        transport replay provenance localName : BHist) :
      HyperbolicPattersonSullivanShadowUp
  deriving DecidableEq

def hyperbolicPattersonSullivanShadowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicPattersonSullivanShadowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicPattersonSullivanShadowEncodeBHist h

def hyperbolicPattersonSullivanShadowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicPattersonSullivanShadowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicPattersonSullivanShadowDecodeBHist tail)

private theorem HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hyperbolicPattersonSullivanShadowDecodeBHist
        (hyperbolicPattersonSullivanShadowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperbolicPattersonSullivanShadowFields :
    HyperbolicPattersonSullivanShadowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicPattersonSullivanShadowUp.mk boundaryBasepoint visualMetric shadowWindow
      countingBudget busemannTransport transport replay provenance localName =>
      [boundaryBasepoint, visualMetric, shadowWindow, countingBudget, busemannTransport,
        transport, replay, provenance, localName]

def hyperbolicPattersonSullivanShadowToEventFlow :
    HyperbolicPattersonSullivanShadowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (hyperbolicPattersonSullivanShadowFields x).map
        hyperbolicPattersonSullivanShadowEncodeBHist

def hyperbolicPattersonSullivanShadowFromEventFlow :
    EventFlow → Option HyperbolicPattersonSullivanShadowUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | boundaryBasepoint :: rest0 =>
      match rest0 with
      | [] => none
      | visualMetric :: rest1 =>
          match rest1 with
          | [] => none
          | shadowWindow :: rest2 =>
              match rest2 with
              | [] => none
              | countingBudget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | busemannTransport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (HyperbolicPattersonSullivanShadowUp.mk
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                boundaryBasepoint)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                visualMetric)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                shadowWindow)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                countingBudget)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                busemannTransport)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                transport)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                replay)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                provenance)
                                              (hyperbolicPattersonSullivanShadowDecodeBHist
                                                localName))
                                      | _ :: _ => none

private theorem HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HyperbolicPattersonSullivanShadowUp,
      hyperbolicPattersonSullivanShadowFromEventFlow
          (hyperbolicPattersonSullivanShadowToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundaryBasepoint visualMetric shadowWindow countingBudget busemannTransport
      transport replay provenance localName =>
      change
        some
          (HyperbolicPattersonSullivanShadowUp.mk
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist boundaryBasepoint))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist visualMetric))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist shadowWindow))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist countingBudget))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist busemannTransport))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist transport))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist replay))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist provenance))
            (hyperbolicPattersonSullivanShadowDecodeBHist
              (hyperbolicPattersonSullivanShadowEncodeBHist localName))) =
          some
            (HyperbolicPattersonSullivanShadowUp.mk boundaryBasepoint visualMetric
              shadowWindow countingBudget busemannTransport transport replay provenance
              localName)
      rw [HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          boundaryBasepoint,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          visualMetric,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          shadowWindow,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          countingBudget,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          busemannTransport,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          transport,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          replay,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          provenance,
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode
          localName]

private theorem HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicPattersonSullivanShadowUp} :
    hyperbolicPattersonSullivanShadowToEventFlow x =
      hyperbolicPattersonSullivanShadowToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicPattersonSullivanShadowFromEventFlow
          (hyperbolicPattersonSullivanShadowToEventFlow x) =
        hyperbolicPattersonSullivanShadowFromEventFlow
          (hyperbolicPattersonSullivanShadowToEventFlow y) :=
    congrArg hyperbolicPattersonSullivanShadowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_round_trip y)))

instance hyperbolicPattersonSullivanShadowBHistCarrier :
    BHistCarrier HyperbolicPattersonSullivanShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicPattersonSullivanShadowToEventFlow
  fromEventFlow := hyperbolicPattersonSullivanShadowFromEventFlow

instance hyperbolicPattersonSullivanShadowChapterTasteGate :
    ChapterTasteGate HyperbolicPattersonSullivanShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicPattersonSullivanShadowFromEventFlow
          (hyperbolicPattersonSullivanShadowToEventFlow x) =
        some x
    exact HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate HyperbolicPattersonSullivanShadowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicPattersonSullivanShadowChapterTasteGate

theorem HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicPattersonSullivanShadowDecodeBHist
          (hyperbolicPattersonSullivanShadowEncodeBHist h) =
        h) ∧
      (∀ x : HyperbolicPattersonSullivanShadowUp,
        hyperbolicPattersonSullivanShadowFromEventFlow
            (hyperbolicPattersonSullivanShadowToEventFlow x) =
          some x) ∧
        (∀ x y : HyperbolicPattersonSullivanShadowUp,
          hyperbolicPattersonSullivanShadowToEventFlow x =
            hyperbolicPattersonSullivanShadowToEventFlow y →
              x = y) ∧
          hyperbolicPattersonSullivanShadowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_decode_encode,
      HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        HyperbolicPattersonSullivanShadowTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.HyperbolicPattersonSullivanShadowUp
