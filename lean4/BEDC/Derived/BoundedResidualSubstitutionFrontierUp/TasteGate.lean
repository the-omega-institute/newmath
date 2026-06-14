import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedResidualSubstitutionFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedResidualSubstitutionFrontierUp : Type where
  | mk (redex residual checker join obstruction transport replay provenance localName : BHist) :
      BoundedResidualSubstitutionFrontierUp
  deriving DecidableEq

def boundedResidualSubstitutionFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedResidualSubstitutionFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedResidualSubstitutionFrontierEncodeBHist h

def boundedResidualSubstitutionFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedResidualSubstitutionFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedResidualSubstitutionFrontierDecodeBHist tail)

private theorem boundedResidualSubstitutionFrontierDecode_encode_bhist :
    ∀ h : BHist,
      boundedResidualSubstitutionFrontierDecodeBHist
        (boundedResidualSubstitutionFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedResidualSubstitutionFrontierToEventFlow :
    BoundedResidualSubstitutionFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedResidualSubstitutionFrontierUp.mk redex residual checker join obstruction transport
      replay provenance localName =>
      [[BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist redex,
        [BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist residual,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist checker,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist join,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedResidualSubstitutionFrontierEncodeBHist localName]

def boundedResidualSubstitutionFrontierFromEventFlow :
    EventFlow → Option BoundedResidualSubstitutionFrontierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | redex :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | residual :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | checker :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | join :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | obstruction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
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
                                                                                (BoundedResidualSubstitutionFrontierUp.mk
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    redex)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    residual)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    checker)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    join)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    obstruction)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    transport)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    replay)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    provenance)
                                                                                  (boundedResidualSubstitutionFrontierDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem boundedResidualSubstitutionFrontier_round_trip :
    ∀ x : BoundedResidualSubstitutionFrontierUp,
      boundedResidualSubstitutionFrontierFromEventFlow
        (boundedResidualSubstitutionFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk redex residual checker join obstruction transport replay provenance localName =>
      change
        some
          (BoundedResidualSubstitutionFrontierUp.mk
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist redex))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist residual))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist checker))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist join))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist obstruction))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist transport))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist replay))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist provenance))
            (boundedResidualSubstitutionFrontierDecodeBHist
              (boundedResidualSubstitutionFrontierEncodeBHist localName))) =
          some
            (BoundedResidualSubstitutionFrontierUp.mk redex residual checker join obstruction
              transport replay provenance localName)
      rw [boundedResidualSubstitutionFrontierDecode_encode_bhist redex,
        boundedResidualSubstitutionFrontierDecode_encode_bhist residual,
        boundedResidualSubstitutionFrontierDecode_encode_bhist checker,
        boundedResidualSubstitutionFrontierDecode_encode_bhist join,
        boundedResidualSubstitutionFrontierDecode_encode_bhist obstruction,
        boundedResidualSubstitutionFrontierDecode_encode_bhist transport,
        boundedResidualSubstitutionFrontierDecode_encode_bhist replay,
        boundedResidualSubstitutionFrontierDecode_encode_bhist provenance,
        boundedResidualSubstitutionFrontierDecode_encode_bhist localName]

private theorem boundedResidualSubstitutionFrontierToEventFlow_injective
    {x y : BoundedResidualSubstitutionFrontierUp} :
    boundedResidualSubstitutionFrontierToEventFlow x =
      boundedResidualSubstitutionFrontierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedResidualSubstitutionFrontierFromEventFlow
          (boundedResidualSubstitutionFrontierToEventFlow x) =
        boundedResidualSubstitutionFrontierFromEventFlow
          (boundedResidualSubstitutionFrontierToEventFlow y) :=
    congrArg boundedResidualSubstitutionFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedResidualSubstitutionFrontier_round_trip x).symm
      (Eq.trans hread (boundedResidualSubstitutionFrontier_round_trip y)))

instance boundedResidualSubstitutionFrontierBHistCarrier :
    BHistCarrier BoundedResidualSubstitutionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedResidualSubstitutionFrontierToEventFlow
  fromEventFlow := boundedResidualSubstitutionFrontierFromEventFlow

instance boundedResidualSubstitutionFrontierChapterTasteGate :
    ChapterTasteGate BoundedResidualSubstitutionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedResidualSubstitutionFrontierFromEventFlow
        (boundedResidualSubstitutionFrontierToEventFlow x) = some x
    exact boundedResidualSubstitutionFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedResidualSubstitutionFrontierToEventFlow_injective heq)

instance boundedResidualSubstitutionFrontierFieldFaithful :
    FieldFaithful BoundedResidualSubstitutionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BoundedResidualSubstitutionFrontierUp.mk redex residual checker join obstruction
        transport replay provenance localName =>
        [redex, residual, checker, join, obstruction, transport, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk redex₁ residual₁ checker₁ join₁ obstruction₁ transport₁ replay₁ provenance₁
        localName₁ =>
        cases y with
        | mk redex₂ residual₂ checker₂ join₂ obstruction₂ transport₂ replay₂ provenance₂
            localName₂ =>
            injection h with hRedex t1
            injection t1 with hResidual t2
            injection t2 with hChecker t3
            injection t3 with hJoin t4
            injection t4 with hObstruction t5
            injection t5 with hTransport t6
            injection t6 with hReplay t7
            injection t7 with hProvenance t8
            injection t8 with hLocalName _
            cases hRedex
            cases hResidual
            cases hChecker
            cases hJoin
            cases hObstruction
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

instance boundedResidualSubstitutionFrontierNontrivial :
    Nontrivial BoundedResidualSubstitutionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedResidualSubstitutionFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedResidualSubstitutionFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedResidualSubstitutionFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedResidualSubstitutionFrontierChapterTasteGate

theorem BoundedResidualSubstitutionFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedResidualSubstitutionFrontierDecodeBHist
        (boundedResidualSubstitutionFrontierEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BoundedResidualSubstitutionFrontierUp) ∧
        Nonempty (ChapterTasteGate BoundedResidualSubstitutionFrontierUp) ∧
          boundedResidualSubstitutionFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨boundedResidualSubstitutionFrontierDecode_encode_bhist,
      ⟨boundedResidualSubstitutionFrontierBHistCarrier⟩,
      ⟨boundedResidualSubstitutionFrontierChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BoundedResidualSubstitutionFrontierUp
