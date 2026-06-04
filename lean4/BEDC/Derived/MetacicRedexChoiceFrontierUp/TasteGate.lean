import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicRedexChoiceFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicRedexChoiceFrontierUp : Type where
  | mk
      (redex normalization confluence decidable replay transport continuation provenance
        classifier tasteBoundary localName : BHist) : MetacicRedexChoiceFrontierUp
  deriving DecidableEq

def metacicRedexChoiceFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicRedexChoiceFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicRedexChoiceFrontierEncodeBHist h

def metacicRedexChoiceFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicRedexChoiceFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicRedexChoiceFrontierDecodeBHist tail)

private theorem metacicRedexChoiceFrontierDecode_encode_bhist :
    ∀ h : BHist,
      metacicRedexChoiceFrontierDecodeBHist
          (metacicRedexChoiceFrontierEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicRedexChoiceFrontierToEventFlow :
    MetacicRedexChoiceFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicRedexChoiceFrontierUp.mk redex normalization confluence decidable replay
      transport continuation provenance classifier tasteBoundary localName =>
      [[BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist redex,
        [BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist normalization,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist confluence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist decidable,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist tasteBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicRedexChoiceFrontierEncodeBHist localName]

private def metacicRedexChoiceFrontierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metacicRedexChoiceFrontierEventAtDefault index rest

def metacicRedexChoiceFrontierFromEventFlow
    (ef : EventFlow) : Option MetacicRedexChoiceFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetacicRedexChoiceFrontierUp.mk
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 1 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 3 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 5 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 7 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 9 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 11 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 13 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 15 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 17 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 19 ef))
      (metacicRedexChoiceFrontierDecodeBHist
        (metacicRedexChoiceFrontierEventAtDefault 21 ef)))

private theorem metacicRedexChoiceFrontier_round_trip :
    ∀ x : MetacicRedexChoiceFrontierUp,
      metacicRedexChoiceFrontierFromEventFlow
          (metacicRedexChoiceFrontierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk redex normalization confluence decidable replay transport continuation provenance
      classifier tasteBoundary localName =>
      change
        some
          (MetacicRedexChoiceFrontierUp.mk
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist redex))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist normalization))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist confluence))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist decidable))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist replay))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist transport))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist continuation))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist provenance))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist classifier))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist tasteBoundary))
            (metacicRedexChoiceFrontierDecodeBHist
              (metacicRedexChoiceFrontierEncodeBHist localName))) =
          some
            (MetacicRedexChoiceFrontierUp.mk redex normalization confluence decidable replay
              transport continuation provenance classifier tasteBoundary localName)
      rw [metacicRedexChoiceFrontierDecode_encode_bhist redex,
        metacicRedexChoiceFrontierDecode_encode_bhist normalization,
        metacicRedexChoiceFrontierDecode_encode_bhist confluence,
        metacicRedexChoiceFrontierDecode_encode_bhist decidable,
        metacicRedexChoiceFrontierDecode_encode_bhist replay,
        metacicRedexChoiceFrontierDecode_encode_bhist transport,
        metacicRedexChoiceFrontierDecode_encode_bhist continuation,
        metacicRedexChoiceFrontierDecode_encode_bhist provenance,
        metacicRedexChoiceFrontierDecode_encode_bhist classifier,
        metacicRedexChoiceFrontierDecode_encode_bhist tasteBoundary,
        metacicRedexChoiceFrontierDecode_encode_bhist localName]

private theorem metacicRedexChoiceFrontierToEventFlow_injective
    {x y : MetacicRedexChoiceFrontierUp} :
    metacicRedexChoiceFrontierToEventFlow x =
        metacicRedexChoiceFrontierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicRedexChoiceFrontierFromEventFlow
          (metacicRedexChoiceFrontierToEventFlow x) =
        metacicRedexChoiceFrontierFromEventFlow
          (metacicRedexChoiceFrontierToEventFlow y) :=
    congrArg metacicRedexChoiceFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicRedexChoiceFrontier_round_trip x).symm
      (Eq.trans hread (metacicRedexChoiceFrontier_round_trip y)))

instance metacicRedexChoiceFrontierBHistCarrier :
    BHistCarrier MetacicRedexChoiceFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicRedexChoiceFrontierToEventFlow
  fromEventFlow := metacicRedexChoiceFrontierFromEventFlow

instance metacicRedexChoiceFrontierChapterTasteGate :
    ChapterTasteGate MetacicRedexChoiceFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicRedexChoiceFrontierFromEventFlow
          (metacicRedexChoiceFrontierToEventFlow x) =
        some x
    exact metacicRedexChoiceFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicRedexChoiceFrontierToEventFlow_injective heq)

instance metacicRedexChoiceFrontierFieldFaithful :
    FieldFaithful MetacicRedexChoiceFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetacicRedexChoiceFrontierUp.mk redex normalization confluence decidable replay
        transport continuation provenance classifier tasteBoundary localName =>
        [redex, normalization, confluence, decidable, replay, transport, continuation,
          provenance, classifier, tasteBoundary, localName]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk redex₁ normalization₁ confluence₁ decidable₁ replay₁ transport₁ continuation₁
        provenance₁ classifier₁ tasteBoundary₁ localName₁ =>
        cases y with
        | mk redex₂ normalization₂ confluence₂ decidable₂ replay₂ transport₂ continuation₂
            provenance₂ classifier₂ tasteBoundary₂ localName₂ =>
            injection h with hRedex rest₁
            injection rest₁ with hNormalization rest₂
            injection rest₂ with hConfluence rest₃
            injection rest₃ with hDecidable rest₄
            injection rest₄ with hReplay rest₅
            injection rest₅ with hTransport rest₆
            injection rest₆ with hContinuation rest₇
            injection rest₇ with hProvenance rest₈
            injection rest₈ with hClassifier rest₉
            injection rest₉ with hTasteBoundary rest₁₀
            injection rest₁₀ with hLocalName _
            cases hRedex
            cases hNormalization
            cases hConfluence
            cases hDecidable
            cases hReplay
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hClassifier
            cases hTasteBoundary
            cases hLocalName
            rfl

instance metacicRedexChoiceFrontierNontrivial :
    Nontrivial MetacicRedexChoiceFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetacicRedexChoiceFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetacicRedexChoiceFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty, by
        intro h
        injection h with hRedex _ _ _ _ _ _ _ _ _ _
        cases hRedex⟩

theorem MetacicRedexChoiceFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicRedexChoiceFrontierDecodeBHist
          (metacicRedexChoiceFrontierEncodeBHist h) =
        h) ∧
      (∀ x : MetacicRedexChoiceFrontierUp,
        metacicRedexChoiceFrontierFromEventFlow
            (metacicRedexChoiceFrontierToEventFlow x) =
          some x) ∧
        (∀ x y : MetacicRedexChoiceFrontierUp,
          metacicRedexChoiceFrontierToEventFlow x =
              metacicRedexChoiceFrontierToEventFlow y ->
            x = y) ∧
          metacicRedexChoiceFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact metacicRedexChoiceFrontierDecode_encode_bhist
  · constructor
    · exact metacicRedexChoiceFrontier_round_trip
    · constructor
      · intro x y heq
        exact metacicRedexChoiceFrontierToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetacicRedexChoiceFrontierUp
