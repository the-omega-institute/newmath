import BEDC.Derived.GeneratorFixedPointUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratorFixedPointUp

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

inductive GeneratorFixedPointUp : Type where
  | mk :
      (generator seed iterate fixedPoint witness route provenance nameCert : BHist) →
      GeneratorFixedPointUp
  deriving DecidableEq

private def generatorFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatorFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatorFixedPointEncodeBHist h

private def generatorFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatorFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatorFixedPointDecodeBHist tail)

private theorem generatorFixedPointDecode_encode_bhist :
    ∀ h : BHist, generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem generatorFixedPoint_mk_congr
    {generator generator' seed seed' iterate iterate' fixedPoint fixedPoint'
      witness witness' route route' provenance provenance' nameCert nameCert' : BHist}
    (hGenerator : generator' = generator)
    (hSeed : seed' = seed)
    (hIterate : iterate' = iterate)
    (hFixedPoint : fixedPoint' = fixedPoint)
    (hWitness : witness' = witness)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    GeneratorFixedPointUp.mk generator' seed' iterate' fixedPoint' witness' route'
        provenance' nameCert' =
      GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGenerator
  cases hSeed
  cases hIterate
  cases hFixedPoint
  cases hWitness
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

private def generatorFixedPointToEventFlow : GeneratorFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route provenance
      nameCert =>
      [[BMark.b0],
        generatorFixedPointEncodeBHist generator,
        [BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist seed,
        [BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist iterate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist fixedPoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        generatorFixedPointEncodeBHist nameCert]

private def generatorFixedPointFromEventFlow : EventFlow → Option GeneratorFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generator :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | seed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | iterate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fixedPoint :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | witness :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (GeneratorFixedPointUp.mk
                                                                          (generatorFixedPointDecodeBHist generator)
                                                                          (generatorFixedPointDecodeBHist seed)
                                                                          (generatorFixedPointDecodeBHist iterate)
                                                                          (generatorFixedPointDecodeBHist fixedPoint)
                                                                          (generatorFixedPointDecodeBHist witness)
                                                                          (generatorFixedPointDecodeBHist route)
                                                                          (generatorFixedPointDecodeBHist provenance)
                                                                          (generatorFixedPointDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem generatorFixedPoint_round_trip :
    ∀ x : GeneratorFixedPointUp,
      generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator seed iterate fixedPoint witness route provenance nameCert =>
      change
        some
          (GeneratorFixedPointUp.mk
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist generator))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist seed))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist iterate))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist fixedPoint))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist witness))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist route))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist provenance))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist nameCert))) =
          some
            (GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route
              provenance nameCert)
      exact
        congrArg some
          (generatorFixedPoint_mk_congr
            (generatorFixedPointDecode_encode_bhist generator)
            (generatorFixedPointDecode_encode_bhist seed)
            (generatorFixedPointDecode_encode_bhist iterate)
            (generatorFixedPointDecode_encode_bhist fixedPoint)
            (generatorFixedPointDecode_encode_bhist witness)
            (generatorFixedPointDecode_encode_bhist route)
            (generatorFixedPointDecode_encode_bhist provenance)
            (generatorFixedPointDecode_encode_bhist nameCert))

private theorem generatorFixedPointToEventFlow_injective {x y : GeneratorFixedPointUp} :
    generatorFixedPointToEventFlow x = generatorFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) =
        generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow y) :=
    congrArg generatorFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (generatorFixedPoint_round_trip x).symm
      (Eq.trans hread (generatorFixedPoint_round_trip y)))

instance generatorFixedPointBHistCarrier : BHistCarrier GeneratorFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatorFixedPointToEventFlow
  fromEventFlow := generatorFixedPointFromEventFlow

instance generatorFixedPointChapterTasteGate : ChapterTasteGate GeneratorFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) = some x
    exact generatorFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (generatorFixedPointToEventFlow_injective heq)

def taste_gate : ChapterTasteGate GeneratorFixedPointUp := generatorFixedPointChapterTasteGate

instance generatorFixedPointFieldFaithful : FieldFaithful GeneratorFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route provenance
        nameCert =>
        [generator, seed, iterate, fixedPoint, witness, route, provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk generator₁ seed₁ iterate₁ fixedPoint₁ witness₁ route₁ provenance₁ nameCert₁ =>
        cases y with
        | mk generator₂ seed₂ iterate₂ fixedPoint₂ witness₂ route₂ provenance₂ nameCert₂ =>
            simp only [] at h
            injection h with hGenerator rest₁
            injection rest₁ with hSeed rest₂
            injection rest₂ with hIterate rest₃
            injection rest₃ with hFixedPoint rest₄
            injection rest₄ with hWitness rest₅
            injection rest₅ with hRoute rest₆
            injection rest₆ with hProvenance rest₇
            injection rest₇ with hNameCert _
            subst hGenerator
            subst hSeed
            subst hIterate
            subst hFixedPoint
            subst hWitness
            subst hRoute
            subst hProvenance
            subst hNameCert
            rfl

theorem GeneratorFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist h) = h) ∧
      (∀ x : GeneratorFixedPointUp,
        generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) = some x) ∧
        (∀ x y : GeneratorFixedPointUp,
          generatorFixedPointToEventFlow x = generatorFixedPointToEventFlow y → x = y) ∧
          generatorFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact generatorFixedPointDecode_encode_bhist
  · constructor
    · exact generatorFixedPoint_round_trip
    · constructor
      · intro x y heq
        exact generatorFixedPointToEventFlow_injective heq
      · rfl

def GeneratorFixedPointCarrier [AskSetup] [PackageSetup]
    (generator list classifier witness output transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generator ∧ UnaryHistory list ∧ UnaryHistory classifier ∧
    UnaryHistory witness ∧ UnaryHistory output ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont generator list classifier ∧ Cont classifier witness output ∧
          Cont transport route provenance ∧ PkgSig bundle provenance pkg

theorem GeneratorFixedPointCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {generator list classifier witness output transport route provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorFixedPointCarrier generator list classifier witness output transport route
        provenance name bundle pkg →
      Cont witness output consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory generator ∧ UnaryHistory list ∧ UnaryHistory classifier ∧
            UnaryHistory witness ∧ UnaryHistory output ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory consumer ∧ Cont generator list classifier ∧
                  Cont classifier witness output ∧ Cont transport route provenance ∧
                    Cont witness output consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumer pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                          (fun row : BHist => hsame row provenance)
                          (fun row : BHist => hsame row provenance ∧
                            PkgSig bundle provenance pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory Pkg
  intro carrier consumerRow consumerPkg
  have generatorUnary : UnaryHistory generator :=
    carrier.left
  have listUnary : UnaryHistory list :=
    carrier.right.left
  have classifierUnary : UnaryHistory classifier :=
    carrier.right.right.left
  have witnessUnary : UnaryHistory witness :=
    carrier.right.right.right.left
  have outputUnary : UnaryHistory output :=
    carrier.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    carrier.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.right.left
  have nameUnary : UnaryHistory name :=
    carrier.right.right.right.right.right.right.right.right.left
  have generatorListClassifier : Cont generator list classifier :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have classifierWitnessOutput : Cont classifier witness output :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have transportRouteProvenance : Cont transport route provenance :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed witnessUnary outputUnary consumerRow
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance
        (And.intro (hsame_refl provenance) provenanceUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left)
          (unary_transport sourceRow.right same)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact
    And.intro generatorUnary
      (And.intro listUnary
        (And.intro classifierUnary
          (And.intro witnessUnary
            (And.intro outputUnary
              (And.intro transportUnary
                (And.intro routeUnary
                  (And.intro provenanceUnary
                    (And.intro nameUnary
                      (And.intro consumerUnary
                        (And.intro generatorListClassifier
                          (And.intro classifierWitnessOutput
                            (And.intro transportRouteProvenance
                              (And.intro consumerRow
                                (And.intro provenancePkg
                                  (And.intro consumerPkg cert)))))))))))))))

end BEDC.Derived.GeneratorFixedPointUp
