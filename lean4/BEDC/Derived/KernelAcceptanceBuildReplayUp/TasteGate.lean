import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelAcceptanceBuildReplayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelAcceptanceBuildReplayUp : Type where
  | mk :
      (generated accepted build replay query transport route provenance name : BHist) →
        KernelAcceptanceBuildReplayUp
  deriving DecidableEq

def kernelAcceptanceBuildReplayEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelAcceptanceBuildReplayEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelAcceptanceBuildReplayEncodeBHist h

def kernelAcceptanceBuildReplayDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelAcceptanceBuildReplayDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelAcceptanceBuildReplayDecodeBHist tail)

private theorem kernelAcceptanceBuildReplayDecode_encode_bhist :
    ∀ h : BHist,
      kernelAcceptanceBuildReplayDecodeBHist
        (kernelAcceptanceBuildReplayEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelAcceptanceBuildReplay_mk_congr
    {generated generated' accepted accepted' build build' replay replay' query query'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hGenerated : generated' = generated)
    (hAccepted : accepted' = accepted)
    (hBuild : build' = build)
    (hReplay : replay' = replay)
    (hQuery : query' = query)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    KernelAcceptanceBuildReplayUp.mk generated' accepted' build' replay' query' transport'
        route' provenance' name' =
      KernelAcceptanceBuildReplayUp.mk generated accepted build replay query transport route
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGenerated
  cases hAccepted
  cases hBuild
  cases hReplay
  cases hQuery
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def kernelAcceptanceBuildReplayToEventFlow :
    KernelAcceptanceBuildReplayUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelAcceptanceBuildReplayUp.mk generated accepted build replay query transport route
      provenance name =>
      [[BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist generated,
        [BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist accepted,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist build,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist query,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelAcceptanceBuildReplayEncodeBHist name]

def kernelAcceptanceBuildReplayFromEventFlow :
    EventFlow → Option KernelAcceptanceBuildReplayUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: generated :: _tag1 :: accepted :: _tag2 :: build :: _tag3 :: replay ::
      _tag4 :: query :: _tag5 :: transport :: _tag6 :: route :: _tag7 :: provenance ::
      _tag8 :: name :: [] =>
      some
        (KernelAcceptanceBuildReplayUp.mk
          (kernelAcceptanceBuildReplayDecodeBHist generated)
          (kernelAcceptanceBuildReplayDecodeBHist accepted)
          (kernelAcceptanceBuildReplayDecodeBHist build)
          (kernelAcceptanceBuildReplayDecodeBHist replay)
          (kernelAcceptanceBuildReplayDecodeBHist query)
          (kernelAcceptanceBuildReplayDecodeBHist transport)
          (kernelAcceptanceBuildReplayDecodeBHist route)
          (kernelAcceptanceBuildReplayDecodeBHist provenance)
          (kernelAcceptanceBuildReplayDecodeBHist name))
  | _ => none

private theorem kernelAcceptanceBuildReplay_round_trip :
    ∀ x : KernelAcceptanceBuildReplayUp,
      kernelAcceptanceBuildReplayFromEventFlow
        (kernelAcceptanceBuildReplayToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generated accepted build replay query transport route provenance name =>
      exact
        congrArg some
          (kernelAcceptanceBuildReplay_mk_congr
            (kernelAcceptanceBuildReplayDecode_encode_bhist generated)
            (kernelAcceptanceBuildReplayDecode_encode_bhist accepted)
            (kernelAcceptanceBuildReplayDecode_encode_bhist build)
            (kernelAcceptanceBuildReplayDecode_encode_bhist replay)
            (kernelAcceptanceBuildReplayDecode_encode_bhist query)
            (kernelAcceptanceBuildReplayDecode_encode_bhist transport)
            (kernelAcceptanceBuildReplayDecode_encode_bhist route)
            (kernelAcceptanceBuildReplayDecode_encode_bhist provenance)
            (kernelAcceptanceBuildReplayDecode_encode_bhist name))

private theorem kernelAcceptanceBuildReplayToEventFlow_injective
    {x y : KernelAcceptanceBuildReplayUp} :
    kernelAcceptanceBuildReplayToEventFlow x =
        kernelAcceptanceBuildReplayToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelAcceptanceBuildReplayFromEventFlow
          (kernelAcceptanceBuildReplayToEventFlow x) =
        kernelAcceptanceBuildReplayFromEventFlow
          (kernelAcceptanceBuildReplayToEventFlow y) :=
    congrArg kernelAcceptanceBuildReplayFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelAcceptanceBuildReplay_round_trip x).symm
      (Eq.trans hread (kernelAcceptanceBuildReplay_round_trip y)))

instance kernelAcceptanceBuildReplayBHistCarrier :
    BHistCarrier KernelAcceptanceBuildReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelAcceptanceBuildReplayToEventFlow
  fromEventFlow := kernelAcceptanceBuildReplayFromEventFlow

instance kernelAcceptanceBuildReplayChapterTasteGate :
    ChapterTasteGate KernelAcceptanceBuildReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelAcceptanceBuildReplayFromEventFlow
          (kernelAcceptanceBuildReplayToEventFlow x) = some x
    exact kernelAcceptanceBuildReplay_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelAcceptanceBuildReplayToEventFlow_injective heq)

instance kernelAcceptanceBuildReplayFieldFaithful :
    FieldFaithful KernelAcceptanceBuildReplayUp where
  fields := fun x =>
    match x with
    | KernelAcceptanceBuildReplayUp.mk generated accepted build replay query transport route
        provenance name =>
        [generated, accepted, build, replay, query, transport, route, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk generated₁ accepted₁ build₁ replay₁ query₁ transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk generated₂ accepted₂ build₂ replay₂ query₂ transport₂ route₂ provenance₂ name₂ =>
        injection h with hGenerated t1
        injection t1 with hAccepted t2
        injection t2 with hBuild t3
        injection t3 with hReplay t4
        injection t4 with hQuery t5
        injection t5 with hTransport t6
        injection t6 with hRoute t7
        injection t7 with hProvenance t8
        injection t8 with hName _
        cases hGenerated
        cases hAccepted
        cases hBuild
        cases hReplay
        cases hQuery
        cases hTransport
        cases hRoute
        cases hProvenance
        cases hName
        rfl

theorem KernelAcceptanceBuildReplayTasteGate_single_carrier_alignment :
    (forall h : BHist,
      kernelAcceptanceBuildReplayDecodeBHist
        (kernelAcceptanceBuildReplayEncodeBHist h) = h) /\
      (forall x : KernelAcceptanceBuildReplayUp,
        kernelAcceptanceBuildReplayFromEventFlow
          (kernelAcceptanceBuildReplayToEventFlow x) = some x) /\
      (forall x y : KernelAcceptanceBuildReplayUp,
        kernelAcceptanceBuildReplayToEventFlow x =
          kernelAcceptanceBuildReplayToEventFlow y -> x = y) /\
      kernelAcceptanceBuildReplayEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelAcceptanceBuildReplayDecode_encode_bhist
  · constructor
    · exact kernelAcceptanceBuildReplay_round_trip
    · constructor
      · intro x y heq
        exact kernelAcceptanceBuildReplayToEventFlow_injective heq
      · rfl

end BEDC.Derived.KernelAcceptanceBuildReplayUp
