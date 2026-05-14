import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# ClosureUniversalityQuadrantUp TasteGate carrier.
-/

namespace BEDC.Derived.ClosureUniversalityQuadrantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite two-axis closure-universality quadrant packet. -/
inductive ClosureUniversalityQuadrantUp : Type where
  | mk :
      (universality closure tag substrate anchors transport routes provenance nameCert : BHist) →
      ClosureUniversalityQuadrantUp
  deriving DecidableEq

def closureUniversalityQuadrantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closureUniversalityQuadrantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closureUniversalityQuadrantEncodeBHist h

def closureUniversalityQuadrantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closureUniversalityQuadrantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closureUniversalityQuadrantDecodeBHist tail)

private theorem closureUniversalityQuadrant_decode_encode_bhist :
    ∀ h : BHist,
      closureUniversalityQuadrantDecodeBHist
        (closureUniversalityQuadrantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem closureUniversalityQuadrant_encode_bhist_injective {h k : BHist} :
    closureUniversalityQuadrantEncodeBHist h =
      closureUniversalityQuadrantEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      closureUniversalityQuadrantDecodeBHist
          (closureUniversalityQuadrantEncodeBHist h) =
        closureUniversalityQuadrantDecodeBHist
          (closureUniversalityQuadrantEncodeBHist k) :=
    congrArg closureUniversalityQuadrantDecodeBHist heq
  rw [closureUniversalityQuadrant_decode_encode_bhist h,
    closureUniversalityQuadrant_decode_encode_bhist k] at hdecode
  exact hdecode

def closureUniversalityQuadrantToEventFlow :
    ClosureUniversalityQuadrantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors transport
      routes provenance nameCert =>
      [[BMark.b0],
        closureUniversalityQuadrantEncodeBHist universality,
        [BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist closure,
        [BMark.b1, BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist tag,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist anchors,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closureUniversalityQuadrantEncodeBHist nameCert]

def closureUniversalityQuadrantFromEventFlow :
    EventFlow → Option ClosureUniversalityQuadrantUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: universality :: _tag1 :: closure :: _tag2 :: tag :: _tag3 :: substrate ::
      _tag4 :: anchors :: _tag5 :: transport :: _tag6 :: routes :: _tag7 :: provenance ::
        _tag8 :: nameCert :: [] =>
      some
        (ClosureUniversalityQuadrantUp.mk
          (closureUniversalityQuadrantDecodeBHist universality)
          (closureUniversalityQuadrantDecodeBHist closure)
          (closureUniversalityQuadrantDecodeBHist tag)
          (closureUniversalityQuadrantDecodeBHist substrate)
          (closureUniversalityQuadrantDecodeBHist anchors)
          (closureUniversalityQuadrantDecodeBHist transport)
          (closureUniversalityQuadrantDecodeBHist routes)
          (closureUniversalityQuadrantDecodeBHist provenance)
          (closureUniversalityQuadrantDecodeBHist nameCert))
  | _ => none

private theorem closureUniversalityQuadrant_round_trip :
    ∀ x : ClosureUniversalityQuadrantUp,
      closureUniversalityQuadrantFromEventFlow
        (closureUniversalityQuadrantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk universality closure tag substrate anchors transport routes provenance nameCert =>
      change
        some
          (ClosureUniversalityQuadrantUp.mk
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist universality))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist closure))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist tag))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist substrate))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist anchors))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist transport))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist routes))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist provenance))
            (closureUniversalityQuadrantDecodeBHist
              (closureUniversalityQuadrantEncodeBHist nameCert))) =
          some
            (ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors
              transport routes provenance nameCert)
      rw [closureUniversalityQuadrant_decode_encode_bhist universality,
        closureUniversalityQuadrant_decode_encode_bhist closure,
        closureUniversalityQuadrant_decode_encode_bhist tag,
        closureUniversalityQuadrant_decode_encode_bhist substrate,
        closureUniversalityQuadrant_decode_encode_bhist anchors,
        closureUniversalityQuadrant_decode_encode_bhist transport,
        closureUniversalityQuadrant_decode_encode_bhist routes,
        closureUniversalityQuadrant_decode_encode_bhist provenance,
        closureUniversalityQuadrant_decode_encode_bhist nameCert]

theorem closureUniversalityQuadrantToEventFlow_injective
    {x y : ClosureUniversalityQuadrantUp} :
    closureUniversalityQuadrantToEventFlow x =
      closureUniversalityQuadrantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk universality₁ closure₁ tag₁ substrate₁ anchors₁ transport₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk universality₂ closure₂ tag₂ substrate₂ anchors₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          injection heq with _ htail₁
          injection htail₁ with huniversality htail₂
          injection htail₂ with _ htail₃
          injection htail₃ with hclosure htail₄
          injection htail₄ with _ htail₅
          injection htail₅ with htag htail₆
          injection htail₆ with _ htail₇
          injection htail₇ with hsubstrate htail₈
          injection htail₈ with _ htail₉
          injection htail₉ with hanchors htail₁₀
          injection htail₁₀ with _ htail₁₁
          injection htail₁₁ with htransport htail₁₂
          injection htail₁₂ with _ htail₁₃
          injection htail₁₃ with hroutes htail₁₄
          injection htail₁₄ with _ htail₁₅
          injection htail₁₅ with hprovenance htail₁₆
          injection htail₁₆ with _ htail₁₇
          injection htail₁₇ with hnameCert _
          have huniversalityEq : universality₁ = universality₂ :=
            closureUniversalityQuadrant_encode_bhist_injective huniversality
          have hclosureEq : closure₁ = closure₂ :=
            closureUniversalityQuadrant_encode_bhist_injective hclosure
          have htagEq : tag₁ = tag₂ :=
            closureUniversalityQuadrant_encode_bhist_injective htag
          have hsubstrateEq : substrate₁ = substrate₂ :=
            closureUniversalityQuadrant_encode_bhist_injective hsubstrate
          have hanchorsEq : anchors₁ = anchors₂ :=
            closureUniversalityQuadrant_encode_bhist_injective hanchors
          have htransportEq : transport₁ = transport₂ :=
            closureUniversalityQuadrant_encode_bhist_injective htransport
          have hroutesEq : routes₁ = routes₂ :=
            closureUniversalityQuadrant_encode_bhist_injective hroutes
          have hprovenanceEq : provenance₁ = provenance₂ :=
            closureUniversalityQuadrant_encode_bhist_injective hprovenance
          have hnameCertEq : nameCert₁ = nameCert₂ :=
            closureUniversalityQuadrant_encode_bhist_injective hnameCert
          cases huniversalityEq
          cases hclosureEq
          cases htagEq
          cases hsubstrateEq
          cases hanchorsEq
          cases htransportEq
          cases hroutesEq
          cases hprovenanceEq
          cases hnameCertEq
          rfl

instance closureUniversalityQuadrantBHistCarrier :
    BHistCarrier ClosureUniversalityQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closureUniversalityQuadrantToEventFlow
  fromEventFlow := closureUniversalityQuadrantFromEventFlow

instance closureUniversalityQuadrantChapterTasteGate :
    ChapterTasteGate ClosureUniversalityQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closureUniversalityQuadrantFromEventFlow
        (closureUniversalityQuadrantToEventFlow x) = some x
    exact closureUniversalityQuadrant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closureUniversalityQuadrantToEventFlow_injective heq)

instance closureUniversalityQuadrantFieldFaithful :
    FieldFaithful ClosureUniversalityQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors transport
        routes provenance nameCert =>
        [universality, closure, tag, substrate, anchors, transport, routes, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk universality₁ closure₁ tag₁ substrate₁ anchors₁ transport₁ routes₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk universality₂ closure₂ tag₂ substrate₂ anchors₂ transport₂ routes₂ provenance₂
            nameCert₂ =>
            cases h
            rfl

instance closureUniversalityQuadrantNontrivial :
    Nontrivial ClosureUniversalityQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosureUniversalityQuadrantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosureUniversalityQuadrantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosureUniversalityQuadrantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closureUniversalityQuadrantChapterTasteGate

def ClosureUniversalityQuadrantTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closureUniversalityQuadrantDecodeBHist
        (closureUniversalityQuadrantEncodeBHist h) = h) ∧
      (∀ x : ClosureUniversalityQuadrantUp,
        closureUniversalityQuadrantFromEventFlow
          (closureUniversalityQuadrantToEventFlow x) = some x) ∧
        (∀ x y : ClosureUniversalityQuadrantUp,
          closureUniversalityQuadrantToEventFlow x =
            closureUniversalityQuadrantToEventFlow y → x = y) ∧
          closureUniversalityQuadrantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact closureUniversalityQuadrant_decode_encode_bhist h
  · constructor
    · intro x
      cases x with
      | mk universality closure tag substrate anchors transport routes provenance nameCert =>
          change
            some
              (ClosureUniversalityQuadrantUp.mk
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist universality))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist closure))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist tag))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist substrate))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist anchors))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist transport))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist routes))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist provenance))
                (closureUniversalityQuadrantDecodeBHist
                  (closureUniversalityQuadrantEncodeBHist nameCert))) =
              some
                (ClosureUniversalityQuadrantUp.mk universality closure tag substrate anchors
                  transport routes provenance nameCert)
          simp only [closureUniversalityQuadrant_decode_encode_bhist]
    · constructor
      · intro x y heq
        exact closureUniversalityQuadrantToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosureUniversalityQuadrantUp
