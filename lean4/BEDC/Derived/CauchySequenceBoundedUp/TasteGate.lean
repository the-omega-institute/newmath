import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceBoundedUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceBoundedUp : Type where
  | mk (S M D R E B H C P N : BHist) : CauchySequenceBoundedUp
  deriving DecidableEq

def cauchySequenceBoundedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceBoundedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceBoundedEncodeBHist h

def cauchySequenceBoundedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceBoundedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceBoundedDecodeBHist tail)

private theorem cauchySequenceBoundedDecode_encode_bhist :
    ∀ h : BHist,
      cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceBoundedFields : CauchySequenceBoundedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceBoundedUp.mk S M D R E B H C P N => [S, M, D, R, E, B, H, C, P, N]

def cauchySequenceBoundedToEventFlow : CauchySequenceBoundedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceBoundedUp.mk S M D R E B H C P N =>
      [[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceBoundedEncodeBHist S,
        cauchySequenceBoundedEncodeBHist M,
        cauchySequenceBoundedEncodeBHist D,
        cauchySequenceBoundedEncodeBHist R,
        cauchySequenceBoundedEncodeBHist E,
        cauchySequenceBoundedEncodeBHist B,
        cauchySequenceBoundedEncodeBHist H,
        cauchySequenceBoundedEncodeBHist C,
        cauchySequenceBoundedEncodeBHist P,
        cauchySequenceBoundedEncodeBHist N]

def cauchySequenceBoundedFromEventFlow : EventFlow → Option CauchySequenceBoundedUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag, S, M, D, R, E, B, H, C, P, N] =>
      some
        (CauchySequenceBoundedUp.mk
          (cauchySequenceBoundedDecodeBHist S)
          (cauchySequenceBoundedDecodeBHist M)
          (cauchySequenceBoundedDecodeBHist D)
          (cauchySequenceBoundedDecodeBHist R)
          (cauchySequenceBoundedDecodeBHist E)
          (cauchySequenceBoundedDecodeBHist B)
          (cauchySequenceBoundedDecodeBHist H)
          (cauchySequenceBoundedDecodeBHist C)
          (cauchySequenceBoundedDecodeBHist P)
          (cauchySequenceBoundedDecodeBHist N))
  | _ => none

private theorem cauchySequenceBounded_round_trip :
    ∀ x : CauchySequenceBoundedUp,
      cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D R E B H C P N =>
      change
        some
          (CauchySequenceBoundedUp.mk
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist S))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist M))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist D))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist R))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist E))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist B))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist H))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist C))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist P))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist N))) =
          some (CauchySequenceBoundedUp.mk S M D R E B H C P N)
      rw [cauchySequenceBoundedDecode_encode_bhist S,
        cauchySequenceBoundedDecode_encode_bhist M,
        cauchySequenceBoundedDecode_encode_bhist D,
        cauchySequenceBoundedDecode_encode_bhist R,
        cauchySequenceBoundedDecode_encode_bhist E,
        cauchySequenceBoundedDecode_encode_bhist B,
        cauchySequenceBoundedDecode_encode_bhist H,
        cauchySequenceBoundedDecode_encode_bhist C,
        cauchySequenceBoundedDecode_encode_bhist P,
        cauchySequenceBoundedDecode_encode_bhist N]

private theorem cauchySequenceBoundedToEventFlow_injective {x y : CauchySequenceBoundedUp} :
    cauchySequenceBoundedToEventFlow x = cauchySequenceBoundedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow x) =
        cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow y) :=
    congrArg cauchySequenceBoundedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceBounded_round_trip x).symm
      (Eq.trans hread (cauchySequenceBounded_round_trip y)))

private theorem cauchySequenceBounded_fields_faithful :
    ∀ x y : CauchySequenceBoundedUp,
      cauchySequenceBoundedFields x = cauchySequenceBoundedFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 M1 D1 R1 E1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 M2 D2 R2 E2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchySequenceBoundedBHistCarrier : BHistCarrier CauchySequenceBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceBoundedToEventFlow
  fromEventFlow := cauchySequenceBoundedFromEventFlow

instance cauchySequenceBoundedChapterTasteGate :
    ChapterTasteGate CauchySequenceBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow x) = some x
    exact cauchySequenceBounded_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceBoundedToEventFlow_injective heq)

instance cauchySequenceBoundedFieldFaithful : FieldFaithful CauchySequenceBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySequenceBoundedFields
  field_faithful := cauchySequenceBounded_fields_faithful

def taste_gate : ChapterTasteGate CauchySequenceBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceBoundedChapterTasteGate

theorem CauchySequenceBoundedTasteGate_single_carrier_alignment :
    (forall h : BHist,
        cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist h) = h) ∧
      cauchySequenceBoundedFields
          (CauchySequenceBoundedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      cauchySequenceBoundedToEventFlow
          (CauchySequenceBoundedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b0, BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], [],
          []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact ⟨cauchySequenceBoundedDecode_encode_bhist, rfl, rfl⟩

def CauchySequenceBoundedCarrier [AskSetup] [PackageSetup]
    (schedule modulus tolerance readback realSeal bound transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory bound ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      Cont schedule modulus tolerance ∧ Cont tolerance bound readback ∧
        Cont readback route realSeal ∧ Cont provenance transport name ∧ PkgSig bundle name pkg

theorem CauchySequenceBoundedCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport route
        provenance name bundle pkg ->
      UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
        UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory bound ∧
          Cont schedule modulus tolerance ∧ Cont tolerance bound readback ∧
            Cont readback route realSeal ∧ hsame name (append provenance transport) ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    _provenanceUnary, scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, readbackUnary, realSealUnary, boundUnary,
      scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal, provenanceTransportName,
      namePkg⟩

theorem CauchySequenceBoundedCarrier_window_bound_handoff [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      boundedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      Cont realSeal bound boundedConsumer ->
        PkgSig bundle boundedConsumer pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory bound ∧
              UnaryHistory boundedConsumer ∧ Cont schedule modulus tolerance ∧
                Cont tolerance bound readback ∧ Cont readback route realSeal ∧
                  Cont realSeal bound boundedConsumer ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle boundedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier realSealBoundConsumer boundedConsumerPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    _provenanceUnary, scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    _provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  have boundedConsumerUnary : UnaryHistory boundedConsumer :=
    unary_cont_closed realSealUnary boundUnary realSealBoundConsumer
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, readbackUnary, realSealUnary, boundUnary,
      boundedConsumerUnary, scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
      realSealBoundConsumer, namePkg, boundedConsumerPkg⟩

theorem CauchySequenceBoundedCarrier_modulus_tail_bound [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      tailBound : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      Cont modulus tolerance tailBound ->
        PkgSig bundle tailBound pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory tailBound ∧ Cont schedule modulus tolerance ∧
              Cont modulus tolerance tailBound ∧ PkgSig bundle name pkg ∧
                PkgSig bundle tailBound pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier modulusToleranceTailBound tailBoundPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, _boundUnary, _routeUnary,
    _provenanceUnary, scheduleModulusTolerance, _toleranceBoundReadback, _readbackRouteSeal,
    _provenanceTransportName, namePkg⟩ := carrier
  have tailBoundUnary : UnaryHistory tailBound :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceTailBound
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, tailBoundUnary, scheduleModulusTolerance,
      modulusToleranceTailBound, namePkg, tailBoundPkg⟩

end BEDC.Derived.CauchySequenceBoundedUp
