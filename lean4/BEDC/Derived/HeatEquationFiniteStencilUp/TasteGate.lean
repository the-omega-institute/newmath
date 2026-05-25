import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeatEquationFiniteStencilUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeatEquationFiniteStencilUp : Type where
  | mk :
      (sourceWindow timeStep spatialStencil boundary finiteReplay realSeal hsameTransport
        contReplay provenance localCert : BHist) →
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

private theorem heatEquationFiniteStencil_decode_encode_bhist :
    ∀ h : BHist,
      heatEquationFiniteStencilDecodeBHist (heatEquationFiniteStencilEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def heatEquationFiniteStencilFields : HeatEquationFiniteStencilUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeatEquationFiniteStencilUp.mk sourceWindow timeStep spatialStencil boundary finiteReplay
      realSeal hsameTransport contReplay provenance localCert =>
      [sourceWindow, timeStep, spatialStencil, boundary, finiteReplay, realSeal,
        hsameTransport, contReplay, provenance, localCert]

def heatEquationFiniteStencilToEventFlow : HeatEquationFiniteStencilUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (heatEquationFiniteStencilFields x).map heatEquationFiniteStencilEncodeBHist

def heatEquationFiniteStencilFromEventFlow : EventFlow → Option HeatEquationFiniteStencilUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceWindow :: rest0 =>
      match rest0 with
      | [] => none
      | timeStep :: rest1 =>
          match rest1 with
          | [] => none
          | spatialStencil :: rest2 =>
              match rest2 with
              | [] => none
              | boundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | finiteReplay :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | hsameTransport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | contReplay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (HeatEquationFiniteStencilUp.mk
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    sourceWindow)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    timeStep)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    spatialStencil)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    boundary)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    finiteReplay)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    realSeal)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    hsameTransport)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    contReplay)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    provenance)
                                                  (heatEquationFiniteStencilDecodeBHist
                                                    localCert))
                                          | _ :: _ => none

private theorem heatEquationFiniteStencil_round_trip :
    ∀ x : HeatEquationFiniteStencilUp,
      heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceWindow timeStep spatialStencil boundary finiteReplay realSeal hsameTransport
      contReplay provenance localCert =>
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
              (heatEquationFiniteStencilEncodeBHist finiteReplay))
            (heatEquationFiniteStencilDecodeBHist
              (heatEquationFiniteStencilEncodeBHist realSeal))
            (heatEquationFiniteStencilDecodeBHist
              (heatEquationFiniteStencilEncodeBHist hsameTransport))
            (heatEquationFiniteStencilDecodeBHist
              (heatEquationFiniteStencilEncodeBHist contReplay))
            (heatEquationFiniteStencilDecodeBHist
              (heatEquationFiniteStencilEncodeBHist provenance))
            (heatEquationFiniteStencilDecodeBHist
              (heatEquationFiniteStencilEncodeBHist localCert))) =
          some
            (HeatEquationFiniteStencilUp.mk sourceWindow timeStep spatialStencil boundary
              finiteReplay realSeal hsameTransport contReplay provenance localCert)
      rw [heatEquationFiniteStencil_decode_encode_bhist sourceWindow,
        heatEquationFiniteStencil_decode_encode_bhist timeStep,
        heatEquationFiniteStencil_decode_encode_bhist spatialStencil,
        heatEquationFiniteStencil_decode_encode_bhist boundary,
        heatEquationFiniteStencil_decode_encode_bhist finiteReplay,
        heatEquationFiniteStencil_decode_encode_bhist realSeal,
        heatEquationFiniteStencil_decode_encode_bhist hsameTransport,
        heatEquationFiniteStencil_decode_encode_bhist contReplay,
        heatEquationFiniteStencil_decode_encode_bhist provenance,
        heatEquationFiniteStencil_decode_encode_bhist localCert]

private theorem heatEquationFiniteStencilToEventFlow_injective
    {x y : HeatEquationFiniteStencilUp} :
    heatEquationFiniteStencilToEventFlow x = heatEquationFiniteStencilToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) =
        heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow y) :=
    congrArg heatEquationFiniteStencilFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (heatEquationFiniteStencil_round_trip x).symm
      (Eq.trans hread (heatEquationFiniteStencil_round_trip y)))

private theorem heatEquationFiniteStencil_fields_faithful :
    ∀ x y : HeatEquationFiniteStencilUp,
      heatEquationFiniteStencilFields x = heatEquationFiniteStencilFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceWindow₁ timeStep₁ spatialStencil₁ boundary₁ finiteReplay₁ realSeal₁
      hsameTransport₁ contReplay₁ provenance₁ localCert₁ =>
      cases y with
      | mk sourceWindow₂ timeStep₂ spatialStencil₂ boundary₂ finiteReplay₂ realSeal₂
          hsameTransport₂ contReplay₂ provenance₂ localCert₂ =>
          injection h with hSourceWindow rest₁
          injection rest₁ with hTimeStep rest₂
          injection rest₂ with hSpatialStencil rest₃
          injection rest₃ with hBoundary rest₄
          injection rest₄ with hFiniteReplay rest₅
          injection rest₅ with hRealSeal rest₆
          injection rest₆ with hHsameTransport rest₇
          injection rest₇ with hContReplay rest₈
          injection rest₈ with hProvenance rest₉
          injection rest₉ with hLocalCert _
          cases hSourceWindow
          cases hTimeStep
          cases hSpatialStencil
          cases hBoundary
          cases hFiniteReplay
          cases hRealSeal
          cases hHsameTransport
          cases hContReplay
          cases hProvenance
          cases hLocalCert
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
    change
      heatEquationFiniteStencilFromEventFlow (heatEquationFiniteStencilToEventFlow x) =
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

namespace TasteGate

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
      heatEquationFiniteStencil_decode_encode_bhist,
      heatEquationFiniteStencil_round_trip,
      (by
        intro x y heq
        exact heatEquationFiniteStencilToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.HeatEquationFiniteStencilUp
