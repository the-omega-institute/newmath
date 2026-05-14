import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalEndpointTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalEndpointTransportUp : Type where
  | mk :
      (sourceProof betaRoute typedEndpoint socket obstruction nonescape transport routes
        provenance name : BHist) →
      ClosedNormalEndpointTransportUp
  deriving DecidableEq

def closedNormalEndpointTransportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalEndpointTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalEndpointTransportEncodeBHist h

def closedNormalEndpointTransportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalEndpointTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalEndpointTransportDecodeBHist tail)

private theorem ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedNormalEndpointTransportDecodeBHist
        (closedNormalEndpointTransportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedNormalEndpointTransportFields :
    ClosedNormalEndpointTransportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalEndpointTransportUp.mk sourceProof betaRoute typedEndpoint socket
      obstruction nonescape transport routes provenance name =>
      [sourceProof, betaRoute, typedEndpoint, socket, obstruction, nonescape,
        transport, routes, provenance, name]

def closedNormalEndpointTransportToEventFlow :
    ClosedNormalEndpointTransportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedNormalEndpointTransportFields x).map
      closedNormalEndpointTransportEncodeBHist

def closedNormalEndpointTransportFromEventFlow :
    EventFlow → Option ClosedNormalEndpointTransportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceProof :: rest0 =>
      match rest0 with
      | [] => none
      | betaRoute :: rest1 =>
          match rest1 with
          | [] => none
          | typedEndpoint :: rest2 =>
              match rest2 with
              | [] => none
              | socket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | obstruction :: rest4 =>
                      match rest4 with
                      | [] => none
                      | nonescape :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ClosedNormalEndpointTransportUp.mk
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    sourceProof)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    betaRoute)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    typedEndpoint)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    socket)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    obstruction)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    nonescape)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    transport)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    routes)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    provenance)
                                                  (closedNormalEndpointTransportDecodeBHist
                                                    name))
                                          | _ :: _ => none

private theorem ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedNormalEndpointTransportUp,
      closedNormalEndpointTransportFromEventFlow
        (closedNormalEndpointTransportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceProof betaRoute typedEndpoint socket obstruction nonescape transport routes
      provenance name =>
      change
        some
          (ClosedNormalEndpointTransportUp.mk
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist sourceProof))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist betaRoute))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist typedEndpoint))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist socket))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist obstruction))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist nonescape))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist transport))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist routes))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist provenance))
            (closedNormalEndpointTransportDecodeBHist
              (closedNormalEndpointTransportEncodeBHist name))) =
          some
            (ClosedNormalEndpointTransportUp.mk sourceProof betaRoute typedEndpoint
              socket obstruction nonescape transport routes provenance name)
      rw [ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          sourceProof,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          betaRoute,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          typedEndpoint,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          socket,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          obstruction,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          nonescape,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          transport,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          routes,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          provenance,
        ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
          name]

private theorem ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_injective
    {x y : ClosedNormalEndpointTransportUp} :
    closedNormalEndpointTransportToEventFlow x =
      closedNormalEndpointTransportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalEndpointTransportFromEventFlow
          (closedNormalEndpointTransportToEventFlow x) =
        closedNormalEndpointTransportFromEventFlow
          (closedNormalEndpointTransportToEventFlow y) :=
    congrArg closedNormalEndpointTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_round_trip y)))

instance closedNormalEndpointTransportBHistCarrier :
    BHistCarrier ClosedNormalEndpointTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalEndpointTransportToEventFlow
  fromEventFlow := closedNormalEndpointTransportFromEventFlow

instance closedNormalEndpointTransportChapterTasteGate :
    ChapterTasteGate ClosedNormalEndpointTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalEndpointTransportFromEventFlow
        (closedNormalEndpointTransportToEventFlow x) = some x
    exact ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_injective heq)

instance closedNormalEndpointTransportFieldFaithful :
    FieldFaithful ClosedNormalEndpointTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedNormalEndpointTransportFields
  field_faithful := by
    intro x y h
    cases x with
    | mk sourceProof₁ betaRoute₁ typedEndpoint₁ socket₁ obstruction₁ nonescape₁
        transport₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk sourceProof₂ betaRoute₂ typedEndpoint₂ socket₂ obstruction₂ nonescape₂
            transport₂ routes₂ provenance₂ name₂ =>
            injection h with hSourceProof hRest₁
            injection hRest₁ with hBetaRoute hRest₂
            injection hRest₂ with hTypedEndpoint hRest₃
            injection hRest₃ with hSocket hRest₄
            injection hRest₄ with hObstruction hRest₅
            injection hRest₅ with hNonescape hRest₆
            injection hRest₆ with hTransport hRest₇
            injection hRest₇ with hRoutes hRest₈
            injection hRest₈ with hProvenance hRest₉
            injection hRest₉ with hName _
            subst hSourceProof
            subst hBetaRoute
            subst hTypedEndpoint
            subst hSocket
            subst hObstruction
            subst hNonescape
            subst hTransport
            subst hRoutes
            subst hProvenance
            subst hName
            rfl

instance closedNormalEndpointTransportNontrivial :
    Nontrivial ClosedNormalEndpointTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedNormalEndpointTransportUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ClosedNormalEndpointTransportUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedNormalEndpointTransportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedNormalEndpointTransportChapterTasteGate

theorem ClosedNormalEndpointTransportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedNormalEndpointTransportDecodeBHist
        (closedNormalEndpointTransportEncodeBHist h) = h) ∧
      (∀ x : ClosedNormalEndpointTransportUp,
        closedNormalEndpointTransportFromEventFlow
          (closedNormalEndpointTransportToEventFlow x) = some x) ∧
        (∀ x y : ClosedNormalEndpointTransportUp,
          closedNormalEndpointTransportToEventFlow x =
            closedNormalEndpointTransportToEventFlow y → x = y) ∧
          closedNormalEndpointTransportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ClosedNormalEndpointTransportTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ClosedNormalEndpointTransportUp
