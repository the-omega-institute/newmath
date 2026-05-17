import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistNonaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistNonaTupleNameCertUp : Type where
  | mk :
      (source target classifier replay lift audit package provenance localName : BHist) →
      BHistNonaTupleNameCertUp
  deriving DecidableEq

def bHistNonaTupleNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistNonaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistNonaTupleNameCertEncodeBHist h

def bHistNonaTupleNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistNonaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistNonaTupleNameCertDecodeBHist tail)

private theorem bHistNonaTupleNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistNonaTupleNameCertDecodeBHist
        (bHistNonaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bHistNonaTupleNameCertToEventFlow :
    BHistNonaTupleNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistNonaTupleNameCertUp.mk source target classifier replay lift audit package provenance
      localName =>
      [[BMark.b0],
        bHistNonaTupleNameCertEncodeBHist source,
        [BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist lift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistNonaTupleNameCertEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistNonaTupleNameCertEncodeBHist localName]

def bHistNonaTupleNameCertFromEventFlow :
    EventFlow → Option BHistNonaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | lift :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | audit :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | package :: rest13 =>
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
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BHistNonaTupleNameCertUp.mk
                                                                                  (bHistNonaTupleNameCertDecodeBHist source)
                                                                                  (bHistNonaTupleNameCertDecodeBHist target)
                                                                                  (bHistNonaTupleNameCertDecodeBHist classifier)
                                                                                  (bHistNonaTupleNameCertDecodeBHist replay)
                                                                                  (bHistNonaTupleNameCertDecodeBHist lift)
                                                                                  (bHistNonaTupleNameCertDecodeBHist audit)
                                                                                  (bHistNonaTupleNameCertDecodeBHist package)
                                                                                  (bHistNonaTupleNameCertDecodeBHist provenance)
                                                                                  (bHistNonaTupleNameCertDecodeBHist localName))
                                                                          | _ :: _ => none

private theorem bHistNonaTupleNameCert_round_trip :
    ∀ x : BHistNonaTupleNameCertUp,
      bHistNonaTupleNameCertFromEventFlow
        (bHistNonaTupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target classifier replay lift audit package provenance localName =>
      change
        some
          (BHistNonaTupleNameCertUp.mk
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist source))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist target))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist classifier))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist replay))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist lift))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist audit))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist package))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist provenance))
            (bHistNonaTupleNameCertDecodeBHist
              (bHistNonaTupleNameCertEncodeBHist localName))) =
          some
            (BHistNonaTupleNameCertUp.mk source target classifier replay lift audit package
              provenance localName)
      rw [bHistNonaTupleNameCertDecode_encode_bhist source,
        bHistNonaTupleNameCertDecode_encode_bhist target,
        bHistNonaTupleNameCertDecode_encode_bhist classifier,
        bHistNonaTupleNameCertDecode_encode_bhist replay,
        bHistNonaTupleNameCertDecode_encode_bhist lift,
        bHistNonaTupleNameCertDecode_encode_bhist audit,
        bHistNonaTupleNameCertDecode_encode_bhist package,
        bHistNonaTupleNameCertDecode_encode_bhist provenance,
        bHistNonaTupleNameCertDecode_encode_bhist localName]

private theorem bHistNonaTupleNameCertToEventFlow_injective
    {x y : BHistNonaTupleNameCertUp} :
    bHistNonaTupleNameCertToEventFlow x =
      bHistNonaTupleNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistNonaTupleNameCertFromEventFlow
          (bHistNonaTupleNameCertToEventFlow x) =
        bHistNonaTupleNameCertFromEventFlow
          (bHistNonaTupleNameCertToEventFlow y) :=
    congrArg bHistNonaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistNonaTupleNameCert_round_trip x).symm
      (Eq.trans hread (bHistNonaTupleNameCert_round_trip y)))

instance bHistNonaTupleNameCertBHistCarrier :
    BHistCarrier BHistNonaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistNonaTupleNameCertToEventFlow
  fromEventFlow := bHistNonaTupleNameCertFromEventFlow

instance bHistNonaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistNonaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistNonaTupleNameCertFromEventFlow
        (bHistNonaTupleNameCertToEventFlow x) = some x
    exact bHistNonaTupleNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistNonaTupleNameCertToEventFlow_injective heq)

instance bHistNonaTupleNameCertFieldFaithful :
    FieldFaithful BHistNonaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BHistNonaTupleNameCertUp.mk source target classifier replay lift audit package
        provenance localName =>
        [source, target, classifier, replay, lift, audit, package, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ target₁ classifier₁ replay₁ lift₁ audit₁ package₁ provenance₁ localName₁ =>
        cases y with
        | mk source₂ target₂ classifier₂ replay₂ lift₂ audit₂ package₂ provenance₂ localName₂ =>
            injection h with hSource t1
            injection t1 with hTarget t2
            injection t2 with hClassifier t3
            injection t3 with hReplay t4
            injection t4 with hLift t5
            injection t5 with hAudit t6
            injection t6 with hPackage t7
            injection t7 with hProvenance t8
            injection t8 with hLocalName _
            cases hSource
            cases hTarget
            cases hClassifier
            cases hReplay
            cases hLift
            cases hAudit
            cases hPackage
            cases hProvenance
            cases hLocalName
            rfl

instance bHistNonaTupleNameCertNontrivial :
    Nontrivial BHistNonaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistNonaTupleNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistNonaTupleNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def bHistNonaTupleNameCertCarrier (h : BHist) : Prop :=
  ∃ x : BHistNonaTupleNameCertUp,
    match x with
    | BHistNonaTupleNameCertUp.mk source target classifier replay lift audit package
        provenance localName =>
        hsame h source ∧ hsame target target ∧ hsame classifier classifier ∧
          hsame replay replay ∧ hsame lift lift ∧ hsame audit audit ∧
            hsame package package ∧ hsame provenance provenance ∧ hsame localName localName

theorem BHistNonaTupleNameCertTasteGate_single_carrier_alignment_semanticNameCert :
    SemanticNameCert bHistNonaTupleNameCertCarrier bHistNonaTupleNameCertCarrier
      bHistNonaTupleNameCertCarrier hsame := by
  -- BEDC touchpoint anchor: BHist NameCert SemanticNameCert hsame
  exact
    NameCert_carrier_self_semantic_lifting {
      carrier_inhabited :=
        ⟨BHist.Empty,
          ⟨BHistNonaTupleNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty⟩⟩
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier
        cases carrier with
        | intro x hx =>
            exact
              ⟨x, hsame_trans (hsame_symm same) hx.left, hx.right⟩
    }

theorem BHistNonaTupleNameCertTasteGate_single_carrier_alignment :
    (∀ h : BHist, bHistNonaTupleNameCertDecodeBHist (bHistNonaTupleNameCertEncodeBHist h) = h) ∧
      (∀ x : BHistNonaTupleNameCertUp,
        bHistNonaTupleNameCertFromEventFlow (bHistNonaTupleNameCertToEventFlow x) = some x) ∧
        (∀ x y : BHistNonaTupleNameCertUp,
          bHistNonaTupleNameCertToEventFlow x = bHistNonaTupleNameCertToEventFlow y ->
            x = y) ∧
          bHistNonaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bHistNonaTupleNameCertDecode_encode_bhist
  · constructor
    · exact bHistNonaTupleNameCert_round_trip
    · constructor
      · intro x y heq
        exact bHistNonaTupleNameCertToEventFlow_injective heq
      · rfl

theorem BHistNonaTupleNameCertLocalNamingNonescape {row localRead : BHist} :
    bHistNonaTupleNameCertCarrier row →
      hsame row localRead →
        SemanticNameCert
          (fun out : BHist => bHistNonaTupleNameCertCarrier row ∧ hsame out localRead)
          (fun out : BHist => hsame out localRead)
          (fun out : BHist => hsame out row ∧ hsame localRead row)
          hsame := by
  -- BEDC touchpoint anchor: BHist NameCert SemanticNameCert hsame
  intro carrierRow rowLocal
  exact {
    core := {
      carrier_inhabited := Exists.intro localRead
        (And.intro carrierRow (hsame_refl localRead))
      equiv_refl := by
        intro out _source
        exact hsame_refl out
      equiv_symm := by
        intro _out _other same
        exact hsame_symm same
      equiv_trans := by
        intro _out _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _out _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _out source
      exact source.right
    ledger_sound := by
      intro _out source
      exact And.intro (hsame_trans source.right (hsame_symm rowLocal)) (hsame_symm rowLocal)
  }

end BEDC.Derived.BHistNonaTupleNameCertUp
