import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RussellAnalysisLadderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RussellAnalysisLadderUp : Type where
  | mk :
      (description context relation stratum witness sameRows routes provenance name :
        BHist) →
      RussellAnalysisLadderUp
  deriving DecidableEq

def russellAnalysisLadderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: russellAnalysisLadderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: russellAnalysisLadderEncodeBHist h

def russellAnalysisLadderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (russellAnalysisLadderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (russellAnalysisLadderDecodeBHist tail)

private theorem russellAnalysisLadderDecode_encode_bhist :
    ∀ h : BHist, russellAnalysisLadderDecodeBHist
      (russellAnalysisLadderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem russellAnalysisLadder_mk_congr
    {description description' context context' relation relation' stratum stratum'
      witness witness' sameRows sameRows' routes routes' provenance provenance'
      name name' : BHist}
    (hDescription : description' = description)
    (hContext : context' = context)
    (hRelation : relation' = relation)
    (hStratum : stratum' = stratum)
    (hWitness : witness' = witness)
    (hSameRows : sameRows' = sameRows)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RussellAnalysisLadderUp.mk description' context' relation' stratum' witness'
        sameRows' routes' provenance' name' =
      RussellAnalysisLadderUp.mk description context relation stratum witness sameRows
        routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hDescription
  cases hContext
  cases hRelation
  cases hStratum
  cases hWitness
  cases hSameRows
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

def russellAnalysisLadderToEventFlow : RussellAnalysisLadderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RussellAnalysisLadderUp.mk description context relation stratum witness sameRows routes
      provenance name =>
      [[BMark.b0],
        russellAnalysisLadderEncodeBHist description,
        [BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist context,
        [BMark.b1, BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist relation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist stratum,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist sameRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        russellAnalysisLadderEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        russellAnalysisLadderEncodeBHist name]

def russellAnalysisLadderFromEventFlow : EventFlow → Option RussellAnalysisLadderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | description :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | context :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | relation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stratum :: rest7 =>
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
                                              | sameRows :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RussellAnalysisLadderUp.mk
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    description)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    context)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    relation)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    stratum)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    witness)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    sameRows)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    routes)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    provenance)
                                                                                  (russellAnalysisLadderDecodeBHist
                                                                                    name))
                                                                          | _ :: _ =>
                                                                              none

private theorem russellAnalysisLadder_round_trip :
    ∀ x : RussellAnalysisLadderUp,
      russellAnalysisLadderFromEventFlow
        (russellAnalysisLadderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk description context relation stratum witness sameRows routes provenance name =>
      change
        some
          (RussellAnalysisLadderUp.mk
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist description))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist context))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist relation))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist stratum))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist witness))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist sameRows))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist routes))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist provenance))
            (russellAnalysisLadderDecodeBHist (russellAnalysisLadderEncodeBHist name))) =
          some
            (RussellAnalysisLadderUp.mk description context relation stratum witness sameRows
              routes provenance name)
      exact
        congrArg some
          (russellAnalysisLadder_mk_congr
            (russellAnalysisLadderDecode_encode_bhist description)
            (russellAnalysisLadderDecode_encode_bhist context)
            (russellAnalysisLadderDecode_encode_bhist relation)
            (russellAnalysisLadderDecode_encode_bhist stratum)
            (russellAnalysisLadderDecode_encode_bhist witness)
            (russellAnalysisLadderDecode_encode_bhist sameRows)
            (russellAnalysisLadderDecode_encode_bhist routes)
            (russellAnalysisLadderDecode_encode_bhist provenance)
            (russellAnalysisLadderDecode_encode_bhist name))

private theorem russellAnalysisLadderToEventFlow_injective
    {x y : RussellAnalysisLadderUp} :
    russellAnalysisLadderToEventFlow x =
      russellAnalysisLadderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      russellAnalysisLadderFromEventFlow (russellAnalysisLadderToEventFlow x) =
        russellAnalysisLadderFromEventFlow (russellAnalysisLadderToEventFlow y) :=
    congrArg russellAnalysisLadderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (russellAnalysisLadder_round_trip x).symm
      (Eq.trans hread (russellAnalysisLadder_round_trip y)))

instance russellAnalysisLadderBHistCarrier : BHistCarrier RussellAnalysisLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := russellAnalysisLadderToEventFlow
  fromEventFlow := russellAnalysisLadderFromEventFlow

instance russellAnalysisLadderChapterTasteGate :
    ChapterTasteGate RussellAnalysisLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      russellAnalysisLadderFromEventFlow
        (russellAnalysisLadderToEventFlow x) = some x
    exact russellAnalysisLadder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (russellAnalysisLadderToEventFlow_injective heq)

instance russellAnalysisLadderFieldFaithful :
    FieldFaithful RussellAnalysisLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RussellAnalysisLadderUp.mk description context relation stratum witness sameRows routes
        provenance name =>
        [description, context, relation, stratum, witness, sameRows, routes, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk description1 context1 relation1 stratum1 witness1 sameRows1 routes1
        provenance1 name1 =>
        cases y with
        | mk description2 context2 relation2 stratum2 witness2 sameRows2 routes2
            provenance2 name2 =>
            injection h with hDescription rest1
            injection rest1 with hContext rest2
            injection rest2 with hRelation rest3
            injection rest3 with hStratum rest4
            injection rest4 with hWitness rest5
            injection rest5 with hSameRows rest6
            injection rest6 with hRoutes rest7
            injection rest7 with hProvenance rest8
            injection rest8 with hName _
            cases hDescription
            cases hContext
            cases hRelation
            cases hStratum
            cases hWitness
            cases hSameRows
            cases hRoutes
            cases hProvenance
            cases hName
            rfl

theorem RussellAnalysisLadderTasteGate_single_carrier_alignment :
    (russellAnalysisLadderDecodeBHist
      (russellAnalysisLadderEncodeBHist BHist.Empty) = BHist.Empty) ∧
      (∀ x : RussellAnalysisLadderUp,
        russellAnalysisLadderFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (∀ x y : RussellAnalysisLadderUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) ∧
          ChapterTasteGate RussellAnalysisLadderUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · intro x
      change
        russellAnalysisLadderFromEventFlow
          (russellAnalysisLadderToEventFlow x) = some x
      exact russellAnalysisLadder_round_trip x
    · constructor
      · intro x y heq
        change
          russellAnalysisLadderToEventFlow x =
            russellAnalysisLadderToEventFlow y at heq
        exact russellAnalysisLadderToEventFlow_injective heq
      · exact russellAnalysisLadderChapterTasteGate

def RussellAnalysisLadderCarrier [AskSetup] [PackageSetup]
    (description context relation stratum witness sameRows routes provenance localCert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont description context relation ∧ Cont stratum witness routes ∧
    Cont sameRows routes provenance ∧ PkgSig bundle localCert pkg

theorem RussellAnalysisLadderCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {description context relation stratum witness sameRows routes provenance localCert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RussellAnalysisLadderCarrier description context relation stratum witness sameRows routes
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RussellAnalysisLadderCarrier description context relation stratum witness sameRows
            routes provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          Cont description context relation ∧ Cont stratum witness routes ∧
            Cont sameRows routes provenance ∧ hsame row localCert)
        (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨descriptionContextRelation, stratumWitnessRoutes, sameRowsRoutesProvenance,
    localCertPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          RussellAnalysisLadderCarrier description context relation stratum witness sameRows
            routes provenance localCert bundle pkg ∧ hsame row localCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro localCert
        (And.intro carrierWitness (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  exact {
    core := certCore
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨descriptionContextRelation, stratumWitnessRoutes, sameRowsRoutesProvenance,
          sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨localCertPkg, sourceRow.right⟩
  }

end BEDC.Derived.RussellAnalysisLadderUp
