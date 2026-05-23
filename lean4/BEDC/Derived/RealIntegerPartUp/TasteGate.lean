import BEDC.Derived.RealIntegerPartUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntegerPartUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realIntegerPartEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntegerPartEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntegerPartEncodeBHist h

def realIntegerPartDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntegerPartDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntegerPartDecodeBHist tail)

private theorem RealIntegerPartTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realIntegerPartDecodeBHist (realIntegerPartEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realIntegerPartFields : RealIntegerPartUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntegerPartUp.mk source bound bracket intCandidate residual dyadicScale
      streamWindow readback transport replay provenance nameRow =>
      [source, bound, bracket, intCandidate, residual, dyadicScale, streamWindow,
        readback, transport, replay, provenance, nameRow]

def realIntegerPartToEventFlow : RealIntegerPartUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realIntegerPartFields x).map realIntegerPartEncodeBHist

def realIntegerPartFromEventFlow : EventFlow → Option RealIntegerPartUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | bound :: rest1 =>
          match rest1 with
          | [] => none
          | bracket :: rest2 =>
              match rest2 with
              | [] => none
              | intCandidate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | residual :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadicScale :: rest5 =>
                          match rest5 with
                          | [] => none
                          | streamWindow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nameRow :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (RealIntegerPartUp.mk
                                                          (realIntegerPartDecodeBHist source)
                                                          (realIntegerPartDecodeBHist bound)
                                                          (realIntegerPartDecodeBHist bracket)
                                                          (realIntegerPartDecodeBHist
                                                            intCandidate)
                                                          (realIntegerPartDecodeBHist residual)
                                                          (realIntegerPartDecodeBHist
                                                            dyadicScale)
                                                          (realIntegerPartDecodeBHist
                                                            streamWindow)
                                                          (realIntegerPartDecodeBHist readback)
                                                          (realIntegerPartDecodeBHist transport)
                                                          (realIntegerPartDecodeBHist replay)
                                                          (realIntegerPartDecodeBHist
                                                            provenance)
                                                          (realIntegerPartDecodeBHist nameRow))
                                                  | _ :: _ => none

private theorem RealIntegerPartTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealIntegerPartUp,
      realIntegerPartFromEventFlow (realIntegerPartToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source bound bracket intCandidate residual dyadicScale streamWindow readback
      transport replay provenance nameRow =>
      change
        some
          (RealIntegerPartUp.mk
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist source))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist bound))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist bracket))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist intCandidate))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist residual))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist dyadicScale))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist streamWindow))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist readback))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist transport))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist replay))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist provenance))
            (realIntegerPartDecodeBHist (realIntegerPartEncodeBHist nameRow))) =
          some
            (RealIntegerPartUp.mk source bound bracket intCandidate residual dyadicScale
              streamWindow readback transport replay provenance nameRow)
      rw [RealIntegerPartTasteGate_single_carrier_alignment_decode_encode source,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode bound,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode bracket,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode intCandidate,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode residual,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode dyadicScale,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode streamWindow,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode readback,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode transport,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode replay,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode provenance,
        RealIntegerPartTasteGate_single_carrier_alignment_decode_encode nameRow]

private theorem RealIntegerPartTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealIntegerPartUp} :
    realIntegerPartToEventFlow x = realIntegerPartToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntegerPartFromEventFlow (realIntegerPartToEventFlow x) =
        realIntegerPartFromEventFlow (realIntegerPartToEventFlow y) :=
    congrArg realIntegerPartFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealIntegerPartTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealIntegerPartTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealIntegerPartTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealIntegerPartUp, realIntegerPartFields x = realIntegerPartFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ bound₁ bracket₁ intCandidate₁ residual₁ dyadicScale₁ streamWindow₁
      readback₁ transport₁ replay₁ provenance₁ nameRow₁ =>
      cases y with
      | mk source₂ bound₂ bracket₂ intCandidate₂ residual₂ dyadicScale₂ streamWindow₂
          readback₂ transport₂ replay₂ provenance₂ nameRow₂ =>
          injection hfields with hSource tail0
          injection tail0 with hBound tail1
          injection tail1 with hBracket tail2
          injection tail2 with hIntCandidate tail3
          injection tail3 with hResidual tail4
          injection tail4 with hDyadicScale tail5
          injection tail5 with hStreamWindow tail6
          injection tail6 with hReadback tail7
          injection tail7 with hTransport tail8
          injection tail8 with hReplay tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hNameRow _
          subst hSource
          subst hBound
          subst hBracket
          subst hIntCandidate
          subst hResidual
          subst hDyadicScale
          subst hStreamWindow
          subst hReadback
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hNameRow
          rfl

instance realIntegerPartBHistCarrier : BHistCarrier RealIntegerPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntegerPartToEventFlow
  fromEventFlow := realIntegerPartFromEventFlow

instance realIntegerPartChapterTasteGate : ChapterTasteGate RealIntegerPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntegerPartFromEventFlow (realIntegerPartToEventFlow x) = some x
    exact RealIntegerPartTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealIntegerPartTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realIntegerPartFieldFaithful : FieldFaithful RealIntegerPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realIntegerPartFields
  field_faithful := RealIntegerPartTasteGate_single_carrier_alignment_fields_faithful

instance realIntegerPartNontrivial : Nontrivial RealIntegerPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealIntegerPartUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealIntegerPartUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealIntegerPartUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntegerPartChapterTasteGate

theorem RealIntegerPartTasteGate_single_carrier_alignment :
    (∀ h : BHist, realIntegerPartDecodeBHist (realIntegerPartEncodeBHist h) = h) ∧
      (∀ x : RealIntegerPartUp,
        realIntegerPartFromEventFlow (realIntegerPartToEventFlow x) = some x) ∧
        (∀ x y : RealIntegerPartUp,
          realIntegerPartToEventFlow x = realIntegerPartToEventFlow y → x = y) ∧
          realIntegerPartEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RealIntegerPartTasteGate_single_carrier_alignment_decode_encode,
      RealIntegerPartTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealIntegerPartTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealIntegerPartUp
