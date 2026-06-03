import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireMetricUp : Type where
  | mk (B W D R U S H C P N : BHist) : BaireMetricUp
  deriving DecidableEq

def baireMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireMetricEncodeBHist h

def baireMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireMetricDecodeBHist tail)

private theorem BaireMetricNamecertObligations_decode :
    ∀ h : BHist, baireMetricDecodeBHist (baireMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def baireMetricToEventFlow : BaireMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BaireMetricUp.mk B W D R U S H C P N =>
      [baireMetricEncodeBHist B,
        baireMetricEncodeBHist W,
        baireMetricEncodeBHist D,
        baireMetricEncodeBHist R,
        baireMetricEncodeBHist U,
        baireMetricEncodeBHist S,
        baireMetricEncodeBHist H,
        baireMetricEncodeBHist C,
        baireMetricEncodeBHist P,
        baireMetricEncodeBHist N]

private def baireMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireMetricEventAtDefault index rest

def baireMetricFromEventFlow (ef : EventFlow) : Option BaireMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireMetricUp.mk
      (baireMetricDecodeBHist (baireMetricEventAtDefault 0 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 1 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 2 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 3 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 4 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 5 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 6 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 7 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 8 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 9 ef)))

private theorem BaireMetricNamecertObligations_round_trip (x : BaireMetricUp) :
    baireMetricFromEventFlow (baireMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B W D R U S H C P N =>
      change
        some
          (BaireMetricUp.mk
            (baireMetricDecodeBHist (baireMetricEncodeBHist B))
            (baireMetricDecodeBHist (baireMetricEncodeBHist W))
            (baireMetricDecodeBHist (baireMetricEncodeBHist D))
            (baireMetricDecodeBHist (baireMetricEncodeBHist R))
            (baireMetricDecodeBHist (baireMetricEncodeBHist U))
            (baireMetricDecodeBHist (baireMetricEncodeBHist S))
            (baireMetricDecodeBHist (baireMetricEncodeBHist H))
            (baireMetricDecodeBHist (baireMetricEncodeBHist C))
            (baireMetricDecodeBHist (baireMetricEncodeBHist P))
            (baireMetricDecodeBHist (baireMetricEncodeBHist N))) =
          some (BaireMetricUp.mk B W D R U S H C P N)
      rw [BaireMetricNamecertObligations_decode B,
        BaireMetricNamecertObligations_decode W,
        BaireMetricNamecertObligations_decode D,
        BaireMetricNamecertObligations_decode R,
        BaireMetricNamecertObligations_decode U,
        BaireMetricNamecertObligations_decode S,
        BaireMetricNamecertObligations_decode H,
        BaireMetricNamecertObligations_decode C,
        BaireMetricNamecertObligations_decode P,
        BaireMetricNamecertObligations_decode N]

private theorem BaireMetricNamecertObligations_toEventFlow_injective
    {x y : BaireMetricUp} :
    baireMetricToEventFlow x = baireMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireMetricFromEventFlow (baireMetricToEventFlow x) =
        baireMetricFromEventFlow (baireMetricToEventFlow y) :=
    congrArg baireMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireMetricNamecertObligations_round_trip x).symm
      (Eq.trans hread (BaireMetricNamecertObligations_round_trip y)))

instance baireMetricBHistCarrier : BHistCarrier BaireMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireMetricToEventFlow
  fromEventFlow := baireMetricFromEventFlow

instance baireMetricChapterTasteGate : ChapterTasteGate BaireMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireMetricFromEventFlow (baireMetricToEventFlow x) = some x
    exact BaireMetricNamecertObligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireMetricNamecertObligations_toEventFlow_injective heq)

theorem BaireMetricNamecertObligations (x : BaireMetricUp) :
    Nonempty (BHistCarrier BaireMetricUp) ∧ Nonempty (ChapterTasteGate BaireMetricUp) ∧
      baireMetricEncodeBHist BHist.Empty = ([] : List BMark) ∧
        baireMetricFromEventFlow (baireMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨baireMetricBHistCarrier⟩, ⟨baireMetricChapterTasteGate⟩, rfl,
      BaireMetricNamecertObligations_round_trip x⟩

def BaireMetricPrefixDistanceCarrier [AskSetup] [PackageSetup]
    (S B W D R U H C P N radiusRead ultrametricRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S B radiusRead ∧
        Cont radiusRead D ultrametricRead ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem BaireMetricRootObservationCarrier [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      UnaryHistory radiusRead ∧ UnaryHistory ultrametricRead ∧ Cont S B radiusRead ∧
        Cont radiusRead D ultrametricRead ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, _unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  exact
    ⟨radiusUnary, ultrametricUnary, radiusRoute, ultrametricRoute, provenancePkg,
      localNamePkg⟩

theorem BaireMetricCarrier_ultrametric_window_stability [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont ultrametricRead R metricRead →
        PkgSig bundle metricRead pkg →
          UnaryHistory radiusRead ∧ UnaryHistory ultrametricRead ∧
            UnaryHistory metricRead ∧ Cont S B radiusRead ∧
              Cont radiusRead D ultrametricRead ∧ Cont ultrametricRead R metricRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle metricRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier metricRoute metricPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed ultrametricUnary unaryR metricRoute
  exact
    ⟨radiusUnary, ultrametricUnary, metricUnary, radiusRoute, ultrametricRoute,
      metricRoute, provenancePkg, metricPkg⟩

theorem BaireMetricUltrametricWindowObligations [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead strongTriangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont ultrametricRead U strongTriangleRead →
        UnaryHistory strongTriangleRead ∧ Cont radiusRead D ultrametricRead ∧
          Cont ultrametricRead U strongTriangleRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont
  intro carrier strongTriangleRoute
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, _unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have strongTriangleUnary : UnaryHistory strongTriangleRead :=
    unary_cont_closed ultrametricUnary unaryU strongTriangleRoute
  exact
    ⟨strongTriangleUnary, ultrametricRoute, strongTriangleRoute, provenancePkg⟩

theorem BaireMetricObligationPrefixCompleteness [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead ultrametricRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B prefixRead →
        Cont ultrametricRead R completeRead →
          UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
            UnaryHistory ultrametricRead ∧ UnaryHistory completeRead ∧
              Cont S B prefixRead ∧ Cont radiusRead D ultrametricRead ∧
                Cont ultrametricRead R completeRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont
  intro carrier prefixRoute completeRoute
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryS unaryB prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed ultrametricUnary unaryR completeRoute
  exact
    ⟨prefixUnary, radiusUnary, ultrametricUnary, completeUnary, prefixRoute,
      ultrametricRoute, completeRoute, provenancePkg⟩

theorem BaireMetricObligationCompleteMetricConsumer [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead ultrametricRead completeRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B prefixRead →
        Cont ultrametricRead R completeRead →
          Cont completeRead U consumerRead →
            PkgSig bundle consumerRead pkg →
              UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                UnaryHistory ultrametricRead ∧ UnaryHistory completeRead ∧
                  UnaryHistory consumerRead ∧ Cont S B prefixRead ∧
                    Cont radiusRead D ultrametricRead ∧
                      Cont ultrametricRead R completeRead ∧
                        Cont completeRead U consumerRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont
  intro carrier prefixRoute completeRoute consumerRoute consumerPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryS unaryB prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed ultrametricUnary unaryR completeRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed completeUnary unaryU consumerRoute
  exact
    ⟨prefixUnary, radiusUnary, ultrametricUnary, completeUnary, consumerUnary,
      prefixRoute, ultrametricRoute, completeRoute, consumerRoute, provenancePkg,
      consumerPkg⟩

theorem BaireMetricZeroRadiusBranch [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg ->
      Cont D BHist.Empty zeroRead ->
        PkgSig bundle zeroRead pkg ->
          UnaryHistory D ∧ UnaryHistory zeroRead ∧ Cont D BHist.Empty zeroRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier zeroRoute zeroPkg
  obtain ⟨_unaryS, _unaryB, _unaryW, unaryD, _unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, _radiusRoute, _ultrametricRoute, provenancePkg,
      _localNamePkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryD unary_empty zeroRoute
  exact ⟨unaryD, zeroUnary, zeroRoute, provenancePkg, zeroPkg⟩

theorem BaireMetricStreamScheduleNonescape [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg ->
      Cont C S replayRead ->
        PkgSig bundle replayRead pkg ->
          UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory replayRead ∧
            Cont C S replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier replayRoute replayPkg
  obtain ⟨unaryS, _unaryB, _unaryW, _unaryD, _unaryR, _unaryU, _unaryH, unaryC,
    _unaryP, _unaryN, _radiusRoute, _ultrametricRoute, provenancePkg,
      _localNamePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryC unaryS replayRoute
  exact ⟨unaryS, unaryC, replayUnary, replayRoute, provenancePkg, replayPkg⟩

theorem BaireMetricCarrier_ultrametric_prefix_route [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead scheduleRead radiusRead metricRead
      ultrametricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W scheduleRead →
          Cont scheduleRead D radiusRead →
            Cont radiusRead R metricRead →
              Cont metricRead U ultrametricRead →
                PkgSig bundle ultrametricRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row ultrametricRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
                          hsame row R ∨ hsame row U ∨ hsame row prefixRead ∨
                            hsame row scheduleRead ∨ hsame row radiusRead ∨
                              hsame row metricRead ∨ hsame row ultrametricRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S B prefixRead ∧
                          Cont prefixRead W scheduleRead ∧
                            Cont scheduleRead D radiusRead ∧
                              Cont radiusRead R metricRead ∧
                                Cont metricRead U ultrametricRead ∧
                                  PkgSig bundle ultrametricRead pkg)
                      hsame ∧
                    UnaryHistory prefixRead ∧ UnaryHistory scheduleRead ∧
                      UnaryHistory radiusRead ∧ UnaryHistory metricRead ∧
                        UnaryHistory ultrametricRead := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier prefixRoute scheduleRoute radiusRoute metricRoute ultrametricRoute
    ultrametricPkg
  obtain ⟨unaryS, unaryB, unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, _carrierRadiusRoute, _carrierUltrametricRoute, _provenancePkg,
      _localNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryS unaryB prefixRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed prefixUnary unaryW scheduleRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed scheduleUnary unaryD radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary unaryR metricRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed metricUnary unaryU ultrametricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ultrametricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row prefixRead ∨ hsame row scheduleRead ∨
                hsame row radiusRead ∨ hsame row metricRead ∨ hsame row ultrametricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W scheduleRead ∧
              Cont scheduleRead D radiusRead ∧ Cont radiusRead R metricRead ∧
                Cont metricRead U ultrametricRead ∧ PkgSig bundle ultrametricRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ultrametricRead ⟨hsame_refl ultrametricRead, ultrametricUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, scheduleRoute, radiusRoute, metricRoute,
          ultrametricRoute, ultrametricPkg⟩
  }
  exact
    ⟨cert, prefixUnary, scheduleUnary, radiusUnary, metricUnary, ultrametricUnary⟩

end BEDC.Derived.BaireMetricUp
