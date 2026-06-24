import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubordinateModulusCoverUp : Type where
  | mk (tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert : BHist) : SubordinateModulusCoverUp
  deriving DecidableEq

def subordinateModulusCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subordinateModulusCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subordinateModulusCoverEncodeBHist h

def subordinateModulusCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subordinateModulusCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subordinateModulusCoverDecodeBHist tail)

private theorem subordinateModulusCoverDecode_encode_bhist :
    ∀ h : BHist, subordinateModulusCoverDecodeBHist
      (subordinateModulusCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subordinateModulusCoverToEventFlow : SubordinateModulusCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
      comparisons transport routes provenance nameCert =>
      [[BMark.b0],
        subordinateModulusCoverEncodeBHist tolerance,
        [BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist bundle,
        [BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist centers,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist radii,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist pointwise,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist coverage,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subordinateModulusCoverEncodeBHist comparisons,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist nameCert]

def subordinateModulusCoverFromEventFlow : EventFlow → Option SubordinateModulusCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | tolerance :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | bundle :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | centers :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | radii :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | precision :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | pointwise :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | coverage :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | comparisons :: rest15 =>
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
                                                                              | routes :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | nameCert :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (SubordinateModulusCoverUp.mk
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            tolerance)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            bundle)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            centers)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            radii)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            precision)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            pointwise)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            coverage)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            comparisons)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            transport)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            routes)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            provenance)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ :: _ => none

private theorem subordinateModulusCover_round_trip :
    ∀ x : SubordinateModulusCoverUp,
      subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert =>
      change
        some (SubordinateModulusCoverUp.mk
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist tolerance))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist bundle))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist centers))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist radii))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist precision))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist pointwise))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist coverage))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist comparisons))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist transport))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist routes))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist provenance))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist nameCert))) =
          some (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise
            coverage comparisons transport routes provenance nameCert)
      rw [subordinateModulusCoverDecode_encode_bhist tolerance,
        subordinateModulusCoverDecode_encode_bhist bundle,
        subordinateModulusCoverDecode_encode_bhist centers,
        subordinateModulusCoverDecode_encode_bhist radii,
        subordinateModulusCoverDecode_encode_bhist precision,
        subordinateModulusCoverDecode_encode_bhist pointwise,
        subordinateModulusCoverDecode_encode_bhist coverage,
        subordinateModulusCoverDecode_encode_bhist comparisons,
        subordinateModulusCoverDecode_encode_bhist transport,
        subordinateModulusCoverDecode_encode_bhist routes,
        subordinateModulusCoverDecode_encode_bhist provenance,
        subordinateModulusCoverDecode_encode_bhist nameCert]

private theorem subordinateModulusCoverToEventFlow_injective {x y : SubordinateModulusCoverUp} :
    subordinateModulusCoverToEventFlow x = subordinateModulusCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) =
        subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow y) :=
    congrArg subordinateModulusCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subordinateModulusCover_round_trip x).symm
      (Eq.trans hread (subordinateModulusCover_round_trip y)))

instance subordinateModulusCoverBHistCarrier : BHistCarrier SubordinateModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subordinateModulusCoverToEventFlow
  fromEventFlow := subordinateModulusCoverFromEventFlow

instance subordinateModulusCoverChapterTasteGate : ChapterTasteGate SubordinateModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x
    exact subordinateModulusCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subordinateModulusCoverToEventFlow_injective heq)

instance subordinateModulusCoverFieldFaithful : FieldFaithful SubordinateModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
        comparisons transport routes provenance nameCert =>
        [tolerance, bundle, centers, radii, precision, pointwise, coverage, comparisons,
          transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk tolerance₁ bundle₁ centers₁ radii₁ precision₁ pointwise₁ coverage₁ comparisons₁
        transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk tolerance₂ bundle₂ centers₂ radii₂ precision₂ pointwise₂ coverage₂ comparisons₂
            transport₂ routes₂ provenance₂ nameCert₂ =>
            injection h with htolerance rest₁
            injection rest₁ with hbundle rest₂
            injection rest₂ with hcenters rest₃
            injection rest₃ with hradii rest₄
            injection rest₄ with hprecision rest₅
            injection rest₅ with hpointwise rest₆
            injection rest₆ with hcoverage rest₇
            injection rest₇ with hcomparisons rest₈
            injection rest₈ with htransport rest₉
            injection rest₉ with hroutes rest₁₀
            injection rest₁₀ with hprovenance rest₁₁
            injection rest₁₁ with hnameCert _
            subst htolerance
            subst hbundle
            subst hcenters
            subst hradii
            subst hprecision
            subst hpointwise
            subst hcoverage
            subst hcomparisons
            subst htransport
            subst hroutes
            subst hprovenance
            subst hnameCert
            rfl

instance subordinateModulusCoverNontrivial : Nontrivial SubordinateModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubordinateModulusCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SubordinateModulusCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SubordinateModulusCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, subordinateModulusCoverDecodeBHist
      (subordinateModulusCoverEncodeBHist h) = h) ∧
      (∀ x : SubordinateModulusCoverUp,
        subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x) ∧
        (∀ x y : SubordinateModulusCoverUp,
          subordinateModulusCoverToEventFlow x = subordinateModulusCoverToEventFlow y → x = y) ∧
          subordinateModulusCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subordinateModulusCoverDecode_encode_bhist
  · constructor
    · exact subordinateModulusCover_round_trip
    · constructor
      · intro x y heq
        exact subordinateModulusCoverToEventFlow_injective heq
      · rfl

theorem SubordinateModulusCoverCarrierObligation {x : SubordinateModulusCoverUp} :
    ∃ tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert : BHist,
      x = SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
        comparisons transport routes provenance nameCert ∧
        subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x ∧
          subordinateModulusCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert =>
      exact
        ⟨tolerance, bundle, centers, radii, precision, pointwise, coverage, comparisons,
          transport, routes, provenance, nameCert, rfl,
          subordinateModulusCover_round_trip
            (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise
              coverage comparisons transport routes provenance nameCert),
          rfl⟩

def SubordinateModulusCoverCarrier [AskSetup] [PackageSetup]
    (E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory E ∧ UnaryHistory bundleSpine ∧ UnaryHistory centers ∧
    UnaryHistory radii ∧ UnaryHistory precision ∧ UnaryHistory pointwise ∧
      UnaryHistory coverage ∧ UnaryHistory comparisons ∧ UnaryHistory transport ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont bundleSpine centers coverage ∧ Cont radii precision comparisons ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem SubordinateModulusCoverLedgerHandoffObligation [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
      comparisons transport route provenance name bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row pointwise ∨ hsame row coverage ∨
                hsame row comparisons ∨ hsame row transport ∨ hsame row route ∨
                  hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bundleSpine centers coverage ∧
              Cont radii precision comparisons ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg)
          hsame ∧ UnaryHistory coverage ∧ UnaryHistory comparisons := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_eUnary, _bundleUnary, _centersUnary, _radiiUnary, _precisionUnary,
    _pointwiseUnary, coverageUnary, comparisonsUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameUnary, coverageRoute, comparisonRoute, provenancePkg, namePkg⟩ :=
    carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row pointwise ∨ hsame row coverage ∨
                hsame row comparisons ∨ hsame row transport ∨ hsame row route ∨
                  hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bundleSpine centers coverage ∧
              Cont radii precision comparisons ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverageRoute, comparisonRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, coverageUnary, comparisonsUnary⟩

theorem SubordinateModulusCoverCompactCoverageExactness [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont centers coverage coverageRead →
        PkgSig bundle coverageRead pkg →
          UnaryHistory bundleSpine ∧ UnaryHistory centers ∧ UnaryHistory coverage ∧
            UnaryHistory coverageRead ∧ Cont centers coverage coverageRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                PkgSig bundle coverageRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier centersCoverageRead coverageReadPkg
  obtain ⟨_eUnary, bundleSpineUnary, centersUnary, _radiiUnary, _precisionUnary,
    _pointwiseUnary, coverageUnary, _comparisonsUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _bundleCoverageRoute, _comparisonRoute, provenancePkg,
    namePkg⟩ := carrier
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed centersUnary coverageUnary centersCoverageRead
  exact
    ⟨bundleSpineUnary, centersUnary, coverageUnary, coverageReadUnary, centersCoverageRead,
      provenancePkg, namePkg, coverageReadPkg⟩

theorem SubordinateModulusCoverPointwiseCompatibility [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name pointwiseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont centers pointwise pointwiseRead →
        PkgSig bundle pointwiseRead pkg →
          UnaryHistory centers ∧ UnaryHistory precision ∧ UnaryHistory pointwise ∧
            UnaryHistory pointwiseRead ∧ Cont centers pointwise pointwiseRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                PkgSig bundle pointwiseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier centersPointwiseRead pointwiseReadPkg
  obtain ⟨_eUnary, _bundleSpineUnary, centersUnary, _radiiUnary, precisionUnary,
    pointwiseUnary, _coverageUnary, _comparisonsUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _bundleCoverageRoute, _comparisonRoute, provenancePkg,
    namePkg⟩ := carrier
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed centersUnary pointwiseUnary centersPointwiseRead
  exact
    ⟨centersUnary, precisionUnary, pointwiseUnary, pointwiseReadUnary, centersPointwiseRead,
      provenancePkg, namePkg, pointwiseReadPkg⟩

theorem SubordinateModulusCoverUniformHandoff
    {tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert : BHist} :
    subordinateModulusCoverFromEventFlow
        (subordinateModulusCoverToEventFlow
          (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
            comparisons transport routes provenance nameCert)) =
        some
          (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
            comparisons transport routes provenance nameCert) ∧
      List.Mem (subordinateModulusCoverEncodeBHist bundle)
        (subordinateModulusCoverToEventFlow
          (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
            comparisons transport routes provenance nameCert)) ∧
        List.Mem (subordinateModulusCoverEncodeBHist centers)
          (subordinateModulusCoverToEventFlow
            (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
              comparisons transport routes provenance nameCert)) ∧
          List.Mem (subordinateModulusCoverEncodeBHist radii)
            (subordinateModulusCoverToEventFlow
              (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise
                coverage comparisons transport routes provenance nameCert)) ∧
            subordinateModulusCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact
      subordinateModulusCover_round_trip
        (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
          comparisons transport routes provenance nameCert)
  · constructor
    · simp only [subordinateModulusCoverToEventFlow]
      exact
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)
    · constructor
      · simp only [subordinateModulusCoverToEventFlow]
        exact
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ (List.Mem.head _)
      · constructor
        · simp only [subordinateModulusCoverToEventFlow]
          exact
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <|
                        List.Mem.tail _ (List.Mem.head _)
        · rfl

theorem SubordinateModulusCoverClassifierStabilityObligation
    {tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert transportedRoutes : BHist} :
    hsame transportedRoutes routes →
      subordinateModulusCoverFromEventFlow
          (subordinateModulusCoverToEventFlow
            (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise
              coverage comparisons transport routes provenance nameCert)) =
          some
            (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise
              coverage comparisons transport routes provenance nameCert) ∧
        hsame transportedRoutes routes ∧
          subordinateModulusCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  intro transportedSameRoutes
  exact
    ⟨subordinateModulusCover_round_trip
        (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
          comparisons transport routes provenance nameCert),
      transportedSameRoutes,
      rfl⟩

end BEDC.Derived.SubordinateModulusCoverUp
