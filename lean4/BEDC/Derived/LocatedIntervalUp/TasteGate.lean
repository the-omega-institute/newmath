import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalUp : Type where
  | mk :
      (lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport
        routes provenance nameCert endpoint : BHist) →
      LocatedIntervalUp
  deriving DecidableEq

def LocatedIntervalTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b0, BMark.b1, BMark.b1]

def LocatedIntervalTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      LocatedIntervalTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      LocatedIntervalTasteGate_single_carrier_alignment_encodeBHist h

def LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem LocatedIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist
          (LocatedIntervalTasteGate_single_carrier_alignment_encodeBHist h) =
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

def LocatedIntervalTasteGate_single_carrier_alignment_fields :
    LocatedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalUp.mk lower upper rationalCells dyadicRefinements streamWindows readbacks
      seals transport routes provenance nameCert endpoint =>
      [lower, upper, rationalCells, dyadicRefinements, streamWindows, readbacks, seals,
        transport, routes, provenance, nameCert, endpoint]

def LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow :
    LocatedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      LocatedIntervalTasteGate_single_carrier_alignment_tag ::
        (LocatedIntervalTasteGate_single_carrier_alignment_fields x).map
          LocatedIntervalTasteGate_single_carrier_alignment_encodeBHist

def LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option LocatedIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, lower, upper, rationalCells, dyadicRefinements, streamWindows, readbacks, seals,
      transport, routes, provenance, nameCert, endpoint] =>
      match tag with
      | [BMark.b0, BMark.b1, BMark.b1] =>
          some
            (LocatedIntervalUp.mk
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist lower)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist upper)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist rationalCells)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist dyadicRefinements)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist streamWindows)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist readbacks)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist seals)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist transport)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist routes)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist provenance)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist nameCert)
              (LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist endpoint))
      | _ => none
  | _ => none

private theorem LocatedIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedIntervalUp,
      LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport
      routes provenance nameCert endpoint =>
      simp only [LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow,
        LocatedIntervalTasteGate_single_carrier_alignment_fields,
        LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, LocatedIntervalTasteGate_single_carrier_alignment_tag,
        LocatedIntervalTasteGate_single_carrier_alignment_decode_encode]

private theorem LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalUp} :
    LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow x =
        LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow x) =
        LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedIntervalTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedIntervalTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : LocatedIntervalUp,
      LocatedIntervalTasteGate_single_carrier_alignment_fields x =
          LocatedIntervalTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lower₁ upper₁ rationalCells₁ dyadicRefinements₁ streamWindows₁ readbacks₁ seals₁
      transport₁ routes₁ provenance₁ nameCert₁ endpoint₁ =>
      cases y with
      | mk lower₂ upper₂ rationalCells₂ dyadicRefinements₂ streamWindows₂ readbacks₂ seals₂
          transport₂ routes₂ provenance₂ nameCert₂ endpoint₂ =>
          injection hfields with hLower tail0
          injection tail0 with hUpper tail1
          injection tail1 with hRationalCells tail2
          injection tail2 with hDyadicRefinements tail3
          injection tail3 with hStreamWindows tail4
          injection tail4 with hReadbacks tail5
          injection tail5 with hSeals tail6
          injection tail6 with hTransport tail7
          injection tail7 with hRoutes tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hNameCert tail10
          injection tail10 with hEndpoint _
          subst hLower
          subst hUpper
          subst hRationalCells
          subst hDyadicRefinements
          subst hStreamWindows
          subst hReadbacks
          subst hSeals
          subst hTransport
          subst hRoutes
          subst hProvenance
          subst hNameCert
          subst hEndpoint
          rfl

instance LocatedIntervalTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier LocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow

instance LocatedIntervalTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate LocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LocatedIntervalTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact LocatedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance LocatedIntervalTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful LocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := LocatedIntervalTasteGate_single_carrier_alignment_fields
  field_faithful := LocatedIntervalTasteGate_single_carrier_alignment_field_faithful

instance LocatedIntervalTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial LocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedIntervalTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocatedIntervalTasteGate_single_carrier_alignment_ChapterTasteGate

theorem LocatedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        LocatedIntervalTasteGate_single_carrier_alignment_decodeBHist
            (LocatedIntervalTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      LocatedIntervalTasteGate_single_carrier_alignment_toEventFlow
          (LocatedIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [[BMark.b0, BMark.b1, BMark.b1], [], [], [], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact LocatedIntervalTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.LocatedIntervalUp
