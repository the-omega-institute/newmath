import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StopCodonZeckendorfSuffixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StopCodonZeckendorfSuffixUp : Type where
  | mk :
      (atlas window suffix legality bridge separation boundary transport route provenance
        name : BHist) →
      StopCodonZeckendorfSuffixUp
  deriving DecidableEq

def stopCodonZeckendorfSuffixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stopCodonZeckendorfSuffixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stopCodonZeckendorfSuffixEncodeBHist h

def stopCodonZeckendorfSuffixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stopCodonZeckendorfSuffixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stopCodonZeckendorfSuffixDecodeBHist tail)

private theorem stopCodonZeckendorfSuffix_decode_encode_bhist :
    ∀ h : BHist,
      stopCodonZeckendorfSuffixDecodeBHist
          (stopCodonZeckendorfSuffixEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stopCodonZeckendorfSuffixFields :
    StopCodonZeckendorfSuffixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StopCodonZeckendorfSuffixUp.mk atlas window suffix legality bridge separation boundary
      transport route provenance name =>
      [atlas, window, suffix, legality, bridge, separation, boundary, transport, route,
        provenance, name]

def stopCodonZeckendorfSuffixToEventFlow :
    StopCodonZeckendorfSuffixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (stopCodonZeckendorfSuffixFields x).map stopCodonZeckendorfSuffixEncodeBHist

def stopCodonZeckendorfSuffixFromEventFlow :
    EventFlow → Option StopCodonZeckendorfSuffixUp
  -- BEDC touchpoint anchor: BHist BMark
  | atlas :: window :: suffix :: legality :: bridge :: separation :: boundary ::
      transport :: route :: provenance :: name :: [] =>
      some
        (StopCodonZeckendorfSuffixUp.mk
          (stopCodonZeckendorfSuffixDecodeBHist atlas)
          (stopCodonZeckendorfSuffixDecodeBHist window)
          (stopCodonZeckendorfSuffixDecodeBHist suffix)
          (stopCodonZeckendorfSuffixDecodeBHist legality)
          (stopCodonZeckendorfSuffixDecodeBHist bridge)
          (stopCodonZeckendorfSuffixDecodeBHist separation)
          (stopCodonZeckendorfSuffixDecodeBHist boundary)
          (stopCodonZeckendorfSuffixDecodeBHist transport)
          (stopCodonZeckendorfSuffixDecodeBHist route)
          (stopCodonZeckendorfSuffixDecodeBHist provenance)
          (stopCodonZeckendorfSuffixDecodeBHist name))
  | _ => none

private theorem stopCodonZeckendorfSuffix_round_trip :
    ∀ x : StopCodonZeckendorfSuffixUp,
      stopCodonZeckendorfSuffixFromEventFlow
          (stopCodonZeckendorfSuffixToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk atlas window suffix legality bridge separation boundary transport route provenance
      name =>
      simp only [stopCodonZeckendorfSuffixToEventFlow, stopCodonZeckendorfSuffixFields,
        stopCodonZeckendorfSuffixFromEventFlow, List.map_cons, List.map_nil,
        stopCodonZeckendorfSuffix_decode_encode_bhist]

private theorem stopCodonZeckendorfSuffixToEventFlow_injective
    {x y : StopCodonZeckendorfSuffixUp} :
    stopCodonZeckendorfSuffixToEventFlow x =
        stopCodonZeckendorfSuffixToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stopCodonZeckendorfSuffixFromEventFlow
          (stopCodonZeckendorfSuffixToEventFlow x) =
        stopCodonZeckendorfSuffixFromEventFlow
          (stopCodonZeckendorfSuffixToEventFlow y) :=
    congrArg stopCodonZeckendorfSuffixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stopCodonZeckendorfSuffix_round_trip x).symm
      (Eq.trans hread (stopCodonZeckendorfSuffix_round_trip y)))

private theorem stopCodonZeckendorfSuffix_field_faithful :
    ∀ x y : StopCodonZeckendorfSuffixUp,
      stopCodonZeckendorfSuffixFields x = stopCodonZeckendorfSuffixFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk atlas₁ window₁ suffix₁ legality₁ bridge₁ separation₁ boundary₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk atlas₂ window₂ suffix₂ legality₂ bridge₂ separation₂ boundary₂ transport₂ route₂
          provenance₂ name₂ =>
          injection hfields with hatlas tail0
          injection tail0 with hwindow tail1
          injection tail1 with hsuffix tail2
          injection tail2 with hlegality tail3
          injection tail3 with hbridge tail4
          injection tail4 with hseparation tail5
          injection tail5 with hboundary tail6
          injection tail6 with htransport tail7
          injection tail7 with hroute tail8
          injection tail8 with hprovenance tail9
          injection tail9 with hname _
          subst hatlas
          subst hwindow
          subst hsuffix
          subst hlegality
          subst hbridge
          subst hseparation
          subst hboundary
          subst htransport
          subst hroute
          subst hprovenance
          subst hname
          rfl

instance stopCodonZeckendorfSuffixBHistCarrier :
    BHistCarrier StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stopCodonZeckendorfSuffixToEventFlow
  fromEventFlow := stopCodonZeckendorfSuffixFromEventFlow

instance stopCodonZeckendorfSuffixChapterTasteGate :
    ChapterTasteGate StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stopCodonZeckendorfSuffixFromEventFlow
          (stopCodonZeckendorfSuffixToEventFlow x) =
        some x
    exact stopCodonZeckendorfSuffix_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stopCodonZeckendorfSuffixToEventFlow_injective heq)

instance stopCodonZeckendorfSuffixFieldFaithful :
    FieldFaithful StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stopCodonZeckendorfSuffixFields
  field_faithful := stopCodonZeckendorfSuffix_field_faithful

instance stopCodonZeckendorfSuffixNontrivial :
    Nontrivial StopCodonZeckendorfSuffixUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StopCodonZeckendorfSuffixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StopCodonZeckendorfSuffixUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StopCodonZeckendorfSuffixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stopCodonZeckendorfSuffixChapterTasteGate

theorem StopCodonZeckendorfSuffixTasteGate_single_carrier_alignment
    (atlas window suffix legality bridge separation boundary transport route provenance
      name : BHist) :
    stopCodonZeckendorfSuffixFields
        (StopCodonZeckendorfSuffixUp.mk atlas window suffix legality bridge separation
          boundary transport route provenance name) =
      [atlas, window, suffix, legality, bridge, separation, boundary, transport, route,
        provenance, name] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  rfl

end BEDC.Derived.StopCodonZeckendorfSuffixUp
