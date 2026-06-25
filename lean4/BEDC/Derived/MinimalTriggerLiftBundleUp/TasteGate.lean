import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalTriggerLiftBundleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalTriggerLiftBundleUp : Type where
  | mk :
      (quotientSupport liftChoice orbitFiber fiberCount liftFlip transport replay provenance
        nameCert : BHist) →
      MinimalTriggerLiftBundleUp
  deriving DecidableEq

def minimalTriggerLiftBundleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalTriggerLiftBundleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalTriggerLiftBundleEncodeBHist h

def minimalTriggerLiftBundleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalTriggerLiftBundleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalTriggerLiftBundleDecodeBHist tail)

private theorem minimalTriggerLiftBundleDecode_encode_bhist :
    ∀ h : BHist,
      minimalTriggerLiftBundleDecodeBHist
        (minimalTriggerLiftBundleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def minimalTriggerLiftBundleToEventFlow :
    MinimalTriggerLiftBundleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalTriggerLiftBundleUp.mk quotientSupport liftChoice orbitFiber fiberCount liftFlip
      transport replay provenance nameCert =>
      [[BMark.b0],
        minimalTriggerLiftBundleEncodeBHist quotientSupport,
        [BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist liftChoice,
        [BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist orbitFiber,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist fiberCount,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist liftFlip,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        minimalTriggerLiftBundleEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        minimalTriggerLiftBundleEncodeBHist nameCert]

def minimalTriggerLiftBundleFromEventFlow :
    EventFlow → Option MinimalTriggerLiftBundleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | quotientSupport :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | liftChoice :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | orbitFiber :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fiberCount :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | liftFlip :: rest9 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MinimalTriggerLiftBundleUp.mk
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    quotientSupport)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    liftChoice)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    orbitFiber)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    fiberCount)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    liftFlip)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    transport)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    replay)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    provenance)
                                                                                  (minimalTriggerLiftBundleDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem minimalTriggerLiftBundle_round_trip :
    ∀ x : MinimalTriggerLiftBundleUp,
      minimalTriggerLiftBundleFromEventFlow
        (minimalTriggerLiftBundleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk quotientSupport liftChoice orbitFiber fiberCount liftFlip transport replay provenance
      nameCert =>
      change
        some
          (MinimalTriggerLiftBundleUp.mk
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist quotientSupport))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist liftChoice))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist orbitFiber))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist fiberCount))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist liftFlip))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist transport))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist replay))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist provenance))
            (minimalTriggerLiftBundleDecodeBHist
              (minimalTriggerLiftBundleEncodeBHist nameCert))) =
          some
            (MinimalTriggerLiftBundleUp.mk quotientSupport liftChoice orbitFiber fiberCount
              liftFlip transport replay provenance nameCert)
      rw [minimalTriggerLiftBundleDecode_encode_bhist quotientSupport,
        minimalTriggerLiftBundleDecode_encode_bhist liftChoice,
        minimalTriggerLiftBundleDecode_encode_bhist orbitFiber,
        minimalTriggerLiftBundleDecode_encode_bhist fiberCount,
        minimalTriggerLiftBundleDecode_encode_bhist liftFlip,
        minimalTriggerLiftBundleDecode_encode_bhist transport,
        minimalTriggerLiftBundleDecode_encode_bhist replay,
        minimalTriggerLiftBundleDecode_encode_bhist provenance,
        minimalTriggerLiftBundleDecode_encode_bhist nameCert]

private theorem minimalTriggerLiftBundleToEventFlow_injective
    {x y : MinimalTriggerLiftBundleUp} :
    minimalTriggerLiftBundleToEventFlow x =
      minimalTriggerLiftBundleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalTriggerLiftBundleFromEventFlow
          (minimalTriggerLiftBundleToEventFlow x) =
        minimalTriggerLiftBundleFromEventFlow
          (minimalTriggerLiftBundleToEventFlow y) :=
    congrArg minimalTriggerLiftBundleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (minimalTriggerLiftBundle_round_trip x).symm
      (Eq.trans hread (minimalTriggerLiftBundle_round_trip y)))

instance minimalTriggerLiftBundleBHistCarrier :
    BHistCarrier MinimalTriggerLiftBundleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalTriggerLiftBundleToEventFlow
  fromEventFlow := minimalTriggerLiftBundleFromEventFlow

instance minimalTriggerLiftBundleChapterTasteGate :
    ChapterTasteGate MinimalTriggerLiftBundleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      minimalTriggerLiftBundleFromEventFlow
        (minimalTriggerLiftBundleToEventFlow x) = some x
    exact minimalTriggerLiftBundle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (minimalTriggerLiftBundleToEventFlow_injective heq)

instance minimalTriggerLiftBundleFieldFaithful :
    FieldFaithful MinimalTriggerLiftBundleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MinimalTriggerLiftBundleUp.mk quotientSupport liftChoice orbitFiber fiberCount liftFlip
        transport replay provenance nameCert =>
        [quotientSupport, liftChoice, orbitFiber, fiberCount, liftFlip, transport, replay,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk quotientSupport₁ liftChoice₁ orbitFiber₁ fiberCount₁ liftFlip₁ transport₁ replay₁
        provenance₁ nameCert₁ =>
        cases y with
        | mk quotientSupport₂ liftChoice₂ orbitFiber₂ fiberCount₂ liftFlip₂ transport₂ replay₂
            provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

instance minimalTriggerLiftBundleNontrivial :
    Nontrivial MinimalTriggerLiftBundleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := ⟨
    MinimalTriggerLiftBundleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    MinimalTriggerLiftBundleUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      intro h
      injection h with sameHead
      cases sameHead
  ⟩

def taste_gate : ChapterTasteGate MinimalTriggerLiftBundleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minimalTriggerLiftBundleChapterTasteGate

theorem MinimalTriggerLiftBundleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      minimalTriggerLiftBundleDecodeBHist
        (minimalTriggerLiftBundleEncodeBHist h) = h) ∧
      (∀ x : MinimalTriggerLiftBundleUp,
        minimalTriggerLiftBundleFromEventFlow
          (minimalTriggerLiftBundleToEventFlow x) = some x) ∧
        (∀ x y : MinimalTriggerLiftBundleUp,
          minimalTriggerLiftBundleToEventFlow x =
            minimalTriggerLiftBundleToEventFlow y → x = y) ∧
          minimalTriggerLiftBundleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact minimalTriggerLiftBundleDecode_encode_bhist
  · constructor
    · exact minimalTriggerLiftBundle_round_trip
    · constructor
      · intro x y heq
        exact minimalTriggerLiftBundleToEventFlow_injective heq
      · rfl

end BEDC.Derived.MinimalTriggerLiftBundleUp
