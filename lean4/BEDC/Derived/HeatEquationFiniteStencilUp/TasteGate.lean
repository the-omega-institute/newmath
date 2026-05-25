import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeatEquationFiniteStencilUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeatEquationFiniteStencilUp : Type where
  | mk
      (sourceWindow timeStep spatialStencil boundary replay realSeal transport continuation
        provenance name : BHist) :
      HeatEquationFiniteStencilUp
  deriving DecidableEq

def heatEquationFiniteStencilEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heatEquationFiniteStencilEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heatEquationFiniteStencilEncodeBHist h

def heatEquationFiniteStencilDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heatEquationFiniteStencilDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heatEquationFiniteStencilDecodeBHist tail)

private theorem heatEquationFiniteStencil_decode_encode :
    ∀ h : BHist,
      heatEquationFiniteStencilDecodeBHist (heatEquationFiniteStencilEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heatEquationFiniteStencilFields : HeatEquationFiniteStencilUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeatEquationFiniteStencilUp.mk sourceWindow timeStep spatialStencil boundary replay realSeal
      transport continuation provenance name =>
      [sourceWindow, timeStep, spatialStencil, boundary, replay, realSeal, transport,
        continuation, provenance, name]

def heatEquationFiniteStencilToEventFlow : HeatEquationFiniteStencilUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (heatEquationFiniteStencilFields x).map heatEquationFiniteStencilEncodeBHist

def heatEquationFiniteStencilFromEventFlow : EventFlow → Option HeatEquationFiniteStencilUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    match flow with
    | [] => none
    | sourceWindow :: rest1 =>
      match rest1 with
      | [] => none
      | timeStep :: rest2 =>
        match rest2 with
        | [] => none
        | spatialStencil :: rest3 =>
          match rest3 with
          | [] => none
          | boundary :: rest4 =>
            match rest4 with
            | [] => none
            | replay :: rest5 =>
              match rest5 with
              | [] => none
              | realSeal :: rest6 =>
                match rest6 with
                | [] => none
                | transport :: rest7 =>
                  match rest7 with
                  | [] => none
                  | continuation :: rest8 =>
                    match rest8 with
                    | [] => none
                    | provenance :: rest9 =>
                      match rest9 with
                      | [] => none
                      | name :: rest10 =>
                        match rest10 with
                        | [] =>
                          some
                            (HeatEquationFiniteStencilUp.mk
                              (heatEquationFiniteStencilDecodeBHist sourceWindow)
                              (heatEquationFiniteStencilDecodeBHist timeStep)
                              (heatEquationFiniteStencilDecodeBHist spatialStencil)
                              (heatEquationFiniteStencilDecodeBHist boundary)
                              (heatEquationFiniteStencilDecodeBHist replay)
                              (heatEquationFiniteStencilDecodeBHist realSeal)
                              (heatEquationFiniteStencilDecodeBHist transport)
                              (heatEquationFiniteStencilDecodeBHist continuation)
                              (heatEquationFiniteStencilDecodeBHist provenance)
                              (heatEquationFiniteStencilDecodeBHist name))
                        | _ :: _ => none

private theorem heatEquationFiniteStencil_round_trip :
    ∀ x : HeatEquationFiniteStencilUp,
      heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk sourceWindow timeStep spatialStencil boundary replay realSeal transport continuation
      provenance name =>
      change
        some
            (HeatEquationFiniteStencilUp.mk
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist sourceWindow))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist timeStep))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist spatialStencil))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist boundary))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist replay))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist realSeal))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist transport))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist continuation))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist provenance))
              (heatEquationFiniteStencilDecodeBHist
                (heatEquationFiniteStencilEncodeBHist name))) =
          some
            (HeatEquationFiniteStencilUp.mk sourceWindow timeStep spatialStencil boundary replay
              realSeal transport continuation provenance name)
      rw [heatEquationFiniteStencil_decode_encode sourceWindow,
        heatEquationFiniteStencil_decode_encode timeStep,
        heatEquationFiniteStencil_decode_encode spatialStencil,
        heatEquationFiniteStencil_decode_encode boundary,
        heatEquationFiniteStencil_decode_encode replay,
        heatEquationFiniteStencil_decode_encode realSeal,
        heatEquationFiniteStencil_decode_encode transport,
        heatEquationFiniteStencil_decode_encode continuation,
        heatEquationFiniteStencil_decode_encode provenance,
        heatEquationFiniteStencil_decode_encode name]

private theorem heatEquationFiniteStencilToEventFlow_injective
    {x y : HeatEquationFiniteStencilUp} :
    heatEquationFiniteStencilToEventFlow x = heatEquationFiniteStencilToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) :=
        (heatEquationFiniteStencil_round_trip x).symm
      _ = heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow y) :=
        congrArg heatEquationFiniteStencilFromEventFlow hxy
      _ = some y := heatEquationFiniteStencil_round_trip y
  cases optionEq
  rfl

private theorem heatEquationFiniteStencil_fields_faithful :
    ∀ x y : HeatEquationFiniteStencilUp,
      heatEquationFiniteStencilFields x = heatEquationFiniteStencilFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceWindow₁ timeStep₁ spatialStencil₁ boundary₁ replay₁ realSeal₁ transport₁
      continuation₁ provenance₁ name₁ =>
      cases y with
      | mk sourceWindow₂ timeStep₂ spatialStencil₂ boundary₂ replay₂ realSeal₂ transport₂
          continuation₂ provenance₂ name₂ =>
          injection h with hSourceWindow rest₁
          injection rest₁ with hTimeStep rest₂
          injection rest₂ with hSpatialStencil rest₃
          injection rest₃ with hBoundary rest₄
          injection rest₄ with hReplay rest₅
          injection rest₅ with hRealSeal rest₆
          injection rest₆ with hTransport rest₇
          injection rest₇ with hContinuation rest₈
          injection rest₈ with hProvenance rest₉
          injection rest₉ with hName _
          cases hSourceWindow
          cases hTimeStep
          cases hSpatialStencil
          cases hBoundary
          cases hReplay
          cases hRealSeal
          cases hTransport
          cases hContinuation
          cases hProvenance
          cases hName
          rfl

instance heatEquationFiniteStencilBHistCarrier : BHistCarrier HeatEquationFiniteStencilUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heatEquationFiniteStencilToEventFlow
  fromEventFlow := heatEquationFiniteStencilFromEventFlow

instance heatEquationFiniteStencilChapterTasteGate :
    ChapterTasteGate HeatEquationFiniteStencilUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) =
      some x
    exact heatEquationFiniteStencil_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (heatEquationFiniteStencilToEventFlow_injective heq)

instance heatEquationFiniteStencilFieldFaithful : FieldFaithful HeatEquationFiniteStencilUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := heatEquationFiniteStencilFields
  field_faithful := heatEquationFiniteStencil_fields_faithful

instance heatEquationFiniteStencilNontrivial : BEDC.Meta.TasteGate.Nontrivial
    HeatEquationFiniteStencilUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HeatEquationFiniteStencilUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HeatEquationFiniteStencilUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HeatEquationFiniteStencilTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HeatEquationFiniteStencilUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heatEquationFiniteStencilChapterTasteGate

theorem HeatEquationFiniteStencilTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HeatEquationFiniteStencilUp) ∧
      Nonempty (FieldFaithful HeatEquationFiniteStencilUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HeatEquationFiniteStencilUp) ∧
          (∀ h : BHist,
            heatEquationFiniteStencilDecodeBHist (heatEquationFiniteStencilEncodeBHist h) =
              h) ∧
            (∀ x : HeatEquationFiniteStencilUp,
              heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) =
                some x) ∧
              (∀ x y : HeatEquationFiniteStencilUp,
                heatEquationFiniteStencilToEventFlow x =
                    heatEquationFiniteStencilToEventFlow y →
                  x = y) ∧
                heatEquationFiniteStencilEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro heatEquationFiniteStencilChapterTasteGate,
      Nonempty.intro heatEquationFiniteStencilFieldFaithful,
      Nonempty.intro heatEquationFiniteStencilNontrivial,
      heatEquationFiniteStencil_decode_encode,
      heatEquationFiniteStencil_round_trip,
      (by
        intro x y heq
        exact heatEquationFiniteStencilToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HeatEquationFiniteStencilUp
