import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CatZeroMetricUp

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

inductive CatZeroMetricUp : Type where
  | mk :
      (metric geodesic vertex edge alexandrov comparison distance ledger transport
        convex package nameCert : BHist) →
      CatZeroMetricUp
  deriving DecidableEq

def catZeroMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: catZeroMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: catZeroMetricEncodeBHist h

def catZeroMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (catZeroMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (catZeroMetricDecodeBHist tail)

private theorem catZeroMetricDecode_encode_bhist :
    ∀ h : BHist, catZeroMetricDecodeBHist (catZeroMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def catZeroMetricToEventFlow : CatZeroMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CatZeroMetricUp.mk metric geodesic vertex edge alexandrov comparison distance ledger
      transport convex package nameCert =>
      [[BMark.b0],
        catZeroMetricEncodeBHist metric,
        [BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist geodesic,
        [BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist vertex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist edge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist alexandrov,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist distance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        catZeroMetricEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist convex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        catZeroMetricEncodeBHist nameCert]

def catZeroMetricFromEventFlow : EventFlow → Option CatZeroMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metric :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | geodesic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | vertex :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | edge :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | alexandrov :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | comparison :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | distance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | convex :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | package :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | nameCert :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (CatZeroMetricUp.mk
                                                                                                          (catZeroMetricDecodeBHist metric)
                                                                                                          (catZeroMetricDecodeBHist geodesic)
                                                                                                          (catZeroMetricDecodeBHist vertex)
                                                                                                          (catZeroMetricDecodeBHist edge)
                                                                                                          (catZeroMetricDecodeBHist alexandrov)
                                                                                                          (catZeroMetricDecodeBHist comparison)
                                                                                                          (catZeroMetricDecodeBHist distance)
                                                                                                          (catZeroMetricDecodeBHist ledger)
                                                                                                          (catZeroMetricDecodeBHist transport)
                                                                                                          (catZeroMetricDecodeBHist convex)
                                                                                                          (catZeroMetricDecodeBHist package)
                                                                                                          (catZeroMetricDecodeBHist nameCert))
                                                                                                  | _ :: _ => none

private theorem catZeroMetric_round_trip :
    ∀ x : CatZeroMetricUp, catZeroMetricFromEventFlow (catZeroMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric geodesic vertex edge alexandrov comparison distance ledger transport convex
      package nameCert =>
      change
        some
          (CatZeroMetricUp.mk
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist metric))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist geodesic))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist vertex))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist edge))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist alexandrov))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist comparison))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist distance))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist ledger))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist transport))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist convex))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist package))
            (catZeroMetricDecodeBHist (catZeroMetricEncodeBHist nameCert))) =
          some
            (CatZeroMetricUp.mk metric geodesic vertex edge alexandrov comparison distance
              ledger transport convex package nameCert)
      rw [catZeroMetricDecode_encode_bhist metric, catZeroMetricDecode_encode_bhist geodesic,
        catZeroMetricDecode_encode_bhist vertex, catZeroMetricDecode_encode_bhist edge,
        catZeroMetricDecode_encode_bhist alexandrov,
        catZeroMetricDecode_encode_bhist comparison,
        catZeroMetricDecode_encode_bhist distance, catZeroMetricDecode_encode_bhist ledger,
        catZeroMetricDecode_encode_bhist transport, catZeroMetricDecode_encode_bhist convex,
        catZeroMetricDecode_encode_bhist package, catZeroMetricDecode_encode_bhist nameCert]

private theorem catZeroMetricToEventFlow_injective {x y : CatZeroMetricUp} :
    catZeroMetricToEventFlow x = catZeroMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      catZeroMetricFromEventFlow (catZeroMetricToEventFlow x) =
        catZeroMetricFromEventFlow (catZeroMetricToEventFlow y) :=
    congrArg catZeroMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (catZeroMetric_round_trip x).symm
      (Eq.trans hread (catZeroMetric_round_trip y)))

def catZeroMetricFields : CatZeroMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CatZeroMetricUp.mk metric geodesic vertex edge alexandrov comparison distance ledger
      transport convex package nameCert =>
      [metric, geodesic, vertex, edge, alexandrov, comparison, distance, ledger, transport,
        convex, package, nameCert]

private theorem catZeroMetric_field_faithful :
    ∀ x y : CatZeroMetricUp, catZeroMetricFields x = catZeroMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric geodesic vertex edge alexandrov comparison distance ledger transport convex
      package nameCert =>
      cases y with
      | mk metric' geodesic' vertex' edge' alexandrov' comparison' distance' ledger'
          transport' convex' package' nameCert' =>
          cases hfields
          rfl

instance catZeroMetricBHistCarrier : BHistCarrier CatZeroMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := catZeroMetricToEventFlow
  fromEventFlow := catZeroMetricFromEventFlow

instance catZeroMetricChapterTasteGate : ChapterTasteGate CatZeroMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change catZeroMetricFromEventFlow (catZeroMetricToEventFlow x) = some x
    exact catZeroMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (catZeroMetricToEventFlow_injective heq)

instance catZeroMetricFieldFaithful : FieldFaithful CatZeroMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := catZeroMetricFields
  field_faithful := catZeroMetric_field_faithful

theorem CatZeroMetricTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CatZeroMetricUp) ∧ Nonempty (ChapterTasteGate CatZeroMetricUp) ∧
      Nonempty (FieldFaithful CatZeroMetricUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨Nonempty.intro catZeroMetricBHistCarrier,
      Nonempty.intro catZeroMetricChapterTasteGate, Nonempty.intro catZeroMetricFieldFaithful⟩

def CatZeroMetricCarrier [AskSetup] [PackageSetup]
    (M G V E A Q D L H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory Q ∧
    Cont M G V ∧ Cont A Q D ∧ Cont Q D L ∧ Cont E L H ∧ Cont H C P ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CatZeroMetricCarrier_comparison_obligations [AskSetup] [PackageSetup]
    {M G V E A Q D L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CatZeroMetricCarrier M G V E A Q D L H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row Q ∧ CatZeroMetricCarrier M G V E A Q D L H C P N bundle pkg)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row V ∨ hsame row E ∨
              hsame row A ∨ hsame row Q ∨ hsame row D ∨ hsame row L ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory Q ∧ Cont M G V ∧
          Cont A Q D := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory hsame
  intro carrier
  rcases carrier with
    ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
      alexandrovComparisonDomain, comparisonDomainHandoff, edgeHandoffTransport,
      transportContinuationProvenance, provenancePkg, localNamePkg⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro Q
            ⟨hsame_refl Q,
              ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
                alexandrovComparisonDomain, comparisonDomainHandoff, edgeHandoffTransport,
                transportContinuationProvenance, provenancePkg, localNamePkg⟩⟩
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
            ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl source.left)))))
      ledger_sound := by
        intro row source
        exact
          ⟨unary_transport comparisonUnary (hsame_symm source.left), provenancePkg,
            localNamePkg⟩
    }
  · exact
      ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
        alexandrovComparisonDomain⟩

theorem CatZeroMetricCarrier_projection_nonescape [AskSetup] [PackageSetup]
    {M G V E A Q D L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CatZeroMetricCarrier M G V E A Q D L H C P N bundle pkg ->
      Cont Q D L ∧ Cont E L H ∧ Cont H C P ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg ∧
          SemanticNameCert
            (fun row : BHist =>
              hsame row L ∧ CatZeroMetricCarrier M G V E A Q D L H C P N bundle pkg)
            (fun row : BHist =>
              hsame row M ∨ hsame row G ∨ hsame row V ∨ hsame row E ∨ hsame row A ∨
                hsame row Q ∨ hsame row D ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N)
            (fun _row : BHist => UnaryHistory Q ∧ Cont Q D L ∧ Cont E L H ∧ Cont H C P)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory
  intro carrier
  rcases carrier with
    ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
      alexandrovComparisonDomain, comparisonDomainHandoff, edgeHandoffTransport,
      transportContinuationProvenance, provenancePkg, localNamePkg⟩
  constructor
  · exact comparisonDomainHandoff
  · constructor
    · exact edgeHandoffTransport
    · constructor
      · exact transportContinuationProvenance
      · constructor
        · exact provenancePkg
        · constructor
          · exact localNamePkg
          · exact {
              core := {
                carrier_inhabited :=
                  Exists.intro L
                    ⟨hsame_refl L,
                      ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
                        alexandrovComparisonDomain, comparisonDomainHandoff,
                        edgeHandoffTransport, transportContinuationProvenance, provenancePkg,
                        localNamePkg⟩⟩
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
                    ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
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
                                (Or.inl source.left)))))))
              ledger_sound := by
                intro _row _source
                exact
                  ⟨comparisonUnary, comparisonDomainHandoff, edgeHandoffTransport,
                    transportContinuationProvenance⟩
            }

end BEDC.Derived.CatZeroMetricUp
