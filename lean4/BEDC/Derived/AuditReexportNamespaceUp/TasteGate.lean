import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditReexportNamespaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditReexportNamespaceUp : Type where
  | mk
      (metaCICNamespace groundCompilerNamespace substrateTags exportAddressLedger
        separationWitness consumerRoute provenance nameCert : BHist) :
      AuditReexportNamespaceUp
  deriving DecidableEq

def auditReexportNamespaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditReexportNamespaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditReexportNamespaceEncodeBHist h

def auditReexportNamespaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditReexportNamespaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditReexportNamespaceDecodeBHist tail)

private theorem auditReexportNamespaceDecode_encode_bhist :
    ∀ h : BHist, auditReexportNamespaceDecodeBHist
      (auditReexportNamespaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem auditReexportNamespace_mk_congr
    {metaCICNamespace metaCICNamespace' groundCompilerNamespace groundCompilerNamespace'
      substrateTags substrateTags' exportAddressLedger exportAddressLedger'
      separationWitness separationWitness' consumerRoute consumerRoute' provenance provenance'
      nameCert nameCert' : BHist}
    (hMetaCICNamespace : metaCICNamespace' = metaCICNamespace)
    (hGroundCompilerNamespace : groundCompilerNamespace' = groundCompilerNamespace)
    (hSubstrateTags : substrateTags' = substrateTags)
    (hExportAddressLedger : exportAddressLedger' = exportAddressLedger)
    (hSeparationWitness : separationWitness' = separationWitness)
    (hConsumerRoute : consumerRoute' = consumerRoute)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    AuditReexportNamespaceUp.mk metaCICNamespace' groundCompilerNamespace' substrateTags'
        exportAddressLedger' separationWitness' consumerRoute' provenance' nameCert' =
      AuditReexportNamespaceUp.mk metaCICNamespace groundCompilerNamespace substrateTags
        exportAddressLedger separationWitness consumerRoute provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetaCICNamespace
  cases hGroundCompilerNamespace
  cases hSubstrateTags
  cases hExportAddressLedger
  cases hSeparationWitness
  cases hConsumerRoute
  cases hProvenance
  cases hNameCert
  rfl

def auditReexportNamespaceToEventFlow : AuditReexportNamespaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditReexportNamespaceUp.mk metaCICNamespace groundCompilerNamespace substrateTags
      exportAddressLedger separationWitness consumerRoute provenance nameCert =>
      [[BMark.b0],
        auditReexportNamespaceEncodeBHist metaCICNamespace,
        [BMark.b1, BMark.b0],
        auditReexportNamespaceEncodeBHist groundCompilerNamespace,
        [BMark.b1, BMark.b1, BMark.b0],
        auditReexportNamespaceEncodeBHist substrateTags,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditReexportNamespaceEncodeBHist exportAddressLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditReexportNamespaceEncodeBHist separationWitness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditReexportNamespaceEncodeBHist consumerRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditReexportNamespaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditReexportNamespaceEncodeBHist nameCert]

def auditReexportNamespaceFromEventFlow :
    EventFlow → Option AuditReexportNamespaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metaCICNamespace :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | groundCompilerNamespace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | substrateTags :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | exportAddressLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | separationWitness :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | consumerRoute :: rest11 =>
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
                                                                        (AuditReexportNamespaceUp.mk
                                                                          (auditReexportNamespaceDecodeBHist metaCICNamespace)
                                                                          (auditReexportNamespaceDecodeBHist groundCompilerNamespace)
                                                                          (auditReexportNamespaceDecodeBHist substrateTags)
                                                                          (auditReexportNamespaceDecodeBHist exportAddressLedger)
                                                                          (auditReexportNamespaceDecodeBHist separationWitness)
                                                                          (auditReexportNamespaceDecodeBHist consumerRoute)
                                                                          (auditReexportNamespaceDecodeBHist provenance)
                                                                          (auditReexportNamespaceDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem auditReexportNamespace_round_trip :
    ∀ x : AuditReexportNamespaceUp,
      auditReexportNamespaceFromEventFlow
        (auditReexportNamespaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metaCICNamespace groundCompilerNamespace substrateTags exportAddressLedger
      separationWitness consumerRoute provenance nameCert =>
      change
        some
          (AuditReexportNamespaceUp.mk
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist metaCICNamespace))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist groundCompilerNamespace))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist substrateTags))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist exportAddressLedger))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist separationWitness))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist consumerRoute))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist provenance))
            (auditReexportNamespaceDecodeBHist
              (auditReexportNamespaceEncodeBHist nameCert))) =
          some
            (AuditReexportNamespaceUp.mk metaCICNamespace groundCompilerNamespace
              substrateTags exportAddressLedger separationWitness consumerRoute provenance
              nameCert)
      exact
        congrArg some
          (auditReexportNamespace_mk_congr
            (auditReexportNamespaceDecode_encode_bhist metaCICNamespace)
            (auditReexportNamespaceDecode_encode_bhist groundCompilerNamespace)
            (auditReexportNamespaceDecode_encode_bhist substrateTags)
            (auditReexportNamespaceDecode_encode_bhist exportAddressLedger)
            (auditReexportNamespaceDecode_encode_bhist separationWitness)
            (auditReexportNamespaceDecode_encode_bhist consumerRoute)
            (auditReexportNamespaceDecode_encode_bhist provenance)
            (auditReexportNamespaceDecode_encode_bhist nameCert))

private theorem auditReexportNamespaceToEventFlow_injective
    {x y : AuditReexportNamespaceUp} :
    auditReexportNamespaceToEventFlow x = auditReexportNamespaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditReexportNamespaceFromEventFlow (auditReexportNamespaceToEventFlow x) =
        auditReexportNamespaceFromEventFlow (auditReexportNamespaceToEventFlow y) :=
    congrArg auditReexportNamespaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditReexportNamespace_round_trip x).symm
      (Eq.trans hread (auditReexportNamespace_round_trip y)))

instance auditReexportNamespaceBHistCarrier : BHistCarrier AuditReexportNamespaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditReexportNamespaceToEventFlow
  fromEventFlow := auditReexportNamespaceFromEventFlow

instance auditReexportNamespaceChapterTasteGate :
    ChapterTasteGate AuditReexportNamespaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditReexportNamespaceFromEventFlow (auditReexportNamespaceToEventFlow x) = some x
    exact auditReexportNamespace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditReexportNamespaceToEventFlow_injective heq)

instance auditReexportNamespaceFieldFaithful :
    FieldFaithful AuditReexportNamespaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditReexportNamespaceUp.mk metaCICNamespace groundCompilerNamespace substrateTags
        exportAddressLedger separationWitness consumerRoute provenance nameCert =>
        [metaCICNamespace, groundCompilerNamespace, substrateTags, exportAddressLedger,
          separationWitness, consumerRoute, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk metaCICNamespace1 groundCompilerNamespace1 substrateTags1 exportAddressLedger1
        separationWitness1 consumerRoute1 provenance1 nameCert1 =>
        cases y with
        | mk metaCICNamespace2 groundCompilerNamespace2 substrateTags2 exportAddressLedger2
            separationWitness2 consumerRoute2 provenance2 nameCert2 =>
            injection h with hMetaCICNamespace t1
            injection t1 with hGroundCompilerNamespace t2
            injection t2 with hSubstrateTags t3
            injection t3 with hExportAddressLedger t4
            injection t4 with hSeparationWitness t5
            injection t5 with hConsumerRoute t6
            injection t6 with hProvenance t7
            injection t7 with hNameCert _
            cases hMetaCICNamespace
            cases hGroundCompilerNamespace
            cases hSubstrateTags
            cases hExportAddressLedger
            cases hSeparationWitness
            cases hConsumerRoute
            cases hProvenance
            cases hNameCert
            rfl

instance auditReexportNamespaceNontrivial : Nontrivial AuditReexportNamespaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditReexportNamespaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AuditReexportNamespaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AuditReexportNamespaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditReexportNamespaceDecodeBHist (auditReexportNamespaceEncodeBHist h) = h) ∧
      (∀ x : AuditReexportNamespaceUp,
        auditReexportNamespaceFromEventFlow (auditReexportNamespaceToEventFlow x) = some x) ∧
        (∀ x y : AuditReexportNamespaceUp,
          auditReexportNamespaceToEventFlow x =
            auditReexportNamespaceToEventFlow y → x = y) ∧
          auditReexportNamespaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditReexportNamespaceDecode_encode_bhist
  · constructor
    · exact auditReexportNamespace_round_trip
    · constructor
      · intro x y heq
        exact auditReexportNamespaceToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditReexportNamespaceUp
