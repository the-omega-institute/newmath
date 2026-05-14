import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SelfTheoryReflectionLoopUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SelfTheoryReflectionLoopUp : Type where
  | mk :
      (identity closureTrace kernelAcceptance auditFamily cyclicReplay boundaryReturn transport
        routes provenance nameCert : BHist) →
      SelfTheoryReflectionLoopUp
  deriving DecidableEq

def selfTheoryReflectionLoopEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: selfTheoryReflectionLoopEncodeBHist h
  | BHist.e1 h => BMark.b1 :: selfTheoryReflectionLoopEncodeBHist h

def selfTheoryReflectionLoopDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (selfTheoryReflectionLoopDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (selfTheoryReflectionLoopDecodeBHist tail)

private theorem selfTheoryReflectionLoopDecode_encode_bhist :
    ∀ h : BHist,
      selfTheoryReflectionLoopDecodeBHist (selfTheoryReflectionLoopEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def selfTheoryReflectionLoopToEventFlow : SelfTheoryReflectionLoopUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SelfTheoryReflectionLoopUp.mk identity closureTrace kernelAcceptance auditFamily
      cyclicReplay boundaryReturn transport routes provenance nameCert =>
      [[BMark.b0],
        selfTheoryReflectionLoopEncodeBHist identity,
        [BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist closureTrace,
        [BMark.b1, BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist kernelAcceptance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist auditFamily,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist cyclicReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist boundaryReturn,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        selfTheoryReflectionLoopEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        selfTheoryReflectionLoopEncodeBHist nameCert]

def selfTheoryReflectionLoopFromEventFlow : EventFlow → Option SelfTheoryReflectionLoopUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | identity :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closureTrace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | kernelAcceptance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditFamily :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | cyclicReplay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | boundaryReturn :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (SelfTheoryReflectionLoopUp.mk
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            identity)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            closureTrace)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            kernelAcceptance)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            auditFamily)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            cyclicReplay)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            boundaryReturn)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            transport)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            routes)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            provenance)
                                                                                          (selfTheoryReflectionLoopDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ => none

private theorem selfTheoryReflectionLoop_round_trip :
    ∀ x : SelfTheoryReflectionLoopUp,
      selfTheoryReflectionLoopFromEventFlow (selfTheoryReflectionLoopToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk identity closureTrace kernelAcceptance auditFamily cyclicReplay boundaryReturn
      transport routes provenance nameCert =>
      change
        some
          (SelfTheoryReflectionLoopUp.mk
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist identity))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist closureTrace))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist kernelAcceptance))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist auditFamily))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist cyclicReplay))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist boundaryReturn))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist transport))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist routes))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist provenance))
            (selfTheoryReflectionLoopDecodeBHist
              (selfTheoryReflectionLoopEncodeBHist nameCert))) =
          some
            (SelfTheoryReflectionLoopUp.mk identity closureTrace kernelAcceptance auditFamily
              cyclicReplay boundaryReturn transport routes provenance nameCert)
      rw [selfTheoryReflectionLoopDecode_encode_bhist identity,
        selfTheoryReflectionLoopDecode_encode_bhist closureTrace,
        selfTheoryReflectionLoopDecode_encode_bhist kernelAcceptance,
        selfTheoryReflectionLoopDecode_encode_bhist auditFamily,
        selfTheoryReflectionLoopDecode_encode_bhist cyclicReplay,
        selfTheoryReflectionLoopDecode_encode_bhist boundaryReturn,
        selfTheoryReflectionLoopDecode_encode_bhist transport,
        selfTheoryReflectionLoopDecode_encode_bhist routes,
        selfTheoryReflectionLoopDecode_encode_bhist provenance,
        selfTheoryReflectionLoopDecode_encode_bhist nameCert]

private theorem selfTheoryReflectionLoopToEventFlow_injective
    {x y : SelfTheoryReflectionLoopUp} :
    selfTheoryReflectionLoopToEventFlow x = selfTheoryReflectionLoopToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      selfTheoryReflectionLoopFromEventFlow (selfTheoryReflectionLoopToEventFlow x) =
        selfTheoryReflectionLoopFromEventFlow (selfTheoryReflectionLoopToEventFlow y) :=
    congrArg selfTheoryReflectionLoopFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (selfTheoryReflectionLoop_round_trip x).symm
      (Eq.trans hread (selfTheoryReflectionLoop_round_trip y)))

instance selfTheoryReflectionLoopBHistCarrier : BHistCarrier SelfTheoryReflectionLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := selfTheoryReflectionLoopToEventFlow
  fromEventFlow := selfTheoryReflectionLoopFromEventFlow

instance selfTheoryReflectionLoopChapterTasteGate :
    ChapterTasteGate SelfTheoryReflectionLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change selfTheoryReflectionLoopFromEventFlow (selfTheoryReflectionLoopToEventFlow x) =
      some x
    exact selfTheoryReflectionLoop_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (selfTheoryReflectionLoopToEventFlow_injective heq)

instance selfTheoryReflectionLoopFieldFaithful : FieldFaithful SelfTheoryReflectionLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SelfTheoryReflectionLoopUp.mk identity closureTrace kernelAcceptance auditFamily
        cyclicReplay boundaryReturn transport routes provenance nameCert =>
        [identity, closureTrace, kernelAcceptance, auditFamily, cyclicReplay,
          boundaryReturn, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk identity₁ closureTrace₁ kernelAcceptance₁ auditFamily₁ cyclicReplay₁
        boundaryReturn₁ transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk identity₂ closureTrace₂ kernelAcceptance₂ auditFamily₂ cyclicReplay₂
            boundaryReturn₂ transport₂ routes₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

instance selfTheoryReflectionLoopNontrivial : Nontrivial SelfTheoryReflectionLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SelfTheoryReflectionLoopUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SelfTheoryReflectionLoopUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SelfTheoryReflectionLoopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  selfTheoryReflectionLoopChapterTasteGate

theorem SelfTheoryReflectionLoopTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SelfTheoryReflectionLoopUp) ∧
      Nonempty (FieldFaithful SelfTheoryReflectionLoopUp) ∧
      Nonempty (Nontrivial SelfTheoryReflectionLoopUp) ∧
        (∀ h : BHist,
          selfTheoryReflectionLoopDecodeBHist (selfTheoryReflectionLoopEncodeBHist h) = h) ∧
          (∀ x : SelfTheoryReflectionLoopUp,
            selfTheoryReflectionLoopFromEventFlow (selfTheoryReflectionLoopToEventFlow x) =
              some x) ∧
            (∀ x y : SelfTheoryReflectionLoopUp,
              selfTheoryReflectionLoopToEventFlow x = selfTheoryReflectionLoopToEventFlow y →
                x = y) ∧
              selfTheoryReflectionLoopEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨selfTheoryReflectionLoopChapterTasteGate⟩
  · constructor
    · exact ⟨selfTheoryReflectionLoopFieldFaithful⟩
    · constructor
      · exact ⟨selfTheoryReflectionLoopNontrivial⟩
      · constructor
        · exact selfTheoryReflectionLoopDecode_encode_bhist
        · constructor
          · exact selfTheoryReflectionLoop_round_trip
          · constructor
            · intro x y heq
              exact selfTheoryReflectionLoopToEventFlow_injective heq
            · rfl

end BEDC.Derived.SelfTheoryReflectionLoopUp
