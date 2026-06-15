import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

/-!
# RealIntervalApartnessUp TasteGate carrier.
-/

namespace BEDC.Derived.RealIntervalApartnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalApartnessUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (leftInterval rightInterval leftLower leftUpper rightLower rightUpper gap finiteWindow
        readback separability transport replay provenance nameCert : BHist) →
      RealIntervalApartnessUp
  deriving DecidableEq

def realIntervalApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalApartnessEncodeBHist h

def realIntervalApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalApartnessDecodeBHist tail)

private theorem realIntervalApartnessDecodeEncodeBHist :
    ∀ h : BHist, realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realIntervalApartnessFields : RealIntervalApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalApartnessUp.mk leftInterval rightInterval leftLower leftUpper rightLower
      rightUpper gap finiteWindow readback separability transport replay provenance nameCert =>
      [leftInterval, rightInterval, leftLower, leftUpper, rightLower, rightUpper, gap,
        finiteWindow, readback, separability, transport, replay, provenance, nameCert]

def realIntervalApartnessToEventFlow : RealIntervalApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalApartnessUp.mk leftInterval rightInterval leftLower leftUpper rightLower
      rightUpper gap finiteWindow readback separability transport replay provenance nameCert =>
      [realIntervalApartnessEncodeBHist leftInterval,
        realIntervalApartnessEncodeBHist rightInterval,
        realIntervalApartnessEncodeBHist leftLower,
        realIntervalApartnessEncodeBHist leftUpper,
        realIntervalApartnessEncodeBHist rightLower,
        realIntervalApartnessEncodeBHist rightUpper,
        realIntervalApartnessEncodeBHist gap,
        realIntervalApartnessEncodeBHist finiteWindow,
        realIntervalApartnessEncodeBHist readback,
        realIntervalApartnessEncodeBHist separability,
        realIntervalApartnessEncodeBHist transport,
        realIntervalApartnessEncodeBHist replay,
        realIntervalApartnessEncodeBHist provenance,
        realIntervalApartnessEncodeBHist nameCert]

def realIntervalApartnessFromEventFlow : EventFlow → Option RealIntervalApartnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | leftInterval :: rest0 =>
      match rest0 with
      | [] => none
      | rightInterval :: rest1 =>
          match rest1 with
          | [] => none
          | leftLower :: rest2 =>
              match rest2 with
              | [] => none
              | leftUpper :: rest3 =>
                  match rest3 with
                  | [] => none
                  | rightLower :: rest4 =>
                      match rest4 with
                      | [] => none
                      | rightUpper :: rest5 =>
                          match rest5 with
                          | [] => none
                          | gap :: rest6 =>
                              match rest6 with
                              | [] => none
                              | finiteWindow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | readback :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | separability :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | transport :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | provenance :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameCert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (RealIntervalApartnessUp.mk
                                                                  (realIntervalApartnessDecodeBHist
                                                                    leftInterval)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    rightInterval)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    leftLower)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    leftUpper)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    rightLower)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    rightUpper)
                                                                  (realIntervalApartnessDecodeBHist gap)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    finiteWindow)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    readback)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    separability)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    transport)
                                                                  (realIntervalApartnessDecodeBHist replay)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    provenance)
                                                                  (realIntervalApartnessDecodeBHist
                                                                    nameCert))
                                                          | _ :: _ => none

private theorem realIntervalApartnessRoundTrip (x : RealIntervalApartnessUp) :
    realIntervalApartnessFromEventFlow (realIntervalApartnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk leftInterval rightInterval leftLower leftUpper rightLower rightUpper gap finiteWindow
      readback separability transport replay provenance nameCert =>
      change
        some
          (RealIntervalApartnessUp.mk
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist leftInterval))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist rightInterval))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist leftLower))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist leftUpper))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist rightLower))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist rightUpper))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist gap))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist finiteWindow))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist readback))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist separability))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist transport))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist replay))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist provenance))
            (realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist nameCert))) =
          some
            (RealIntervalApartnessUp.mk leftInterval rightInterval leftLower leftUpper
              rightLower rightUpper gap finiteWindow readback separability transport replay
              provenance nameCert)
      rw [realIntervalApartnessDecodeEncodeBHist leftInterval,
        realIntervalApartnessDecodeEncodeBHist rightInterval,
        realIntervalApartnessDecodeEncodeBHist leftLower,
        realIntervalApartnessDecodeEncodeBHist leftUpper,
        realIntervalApartnessDecodeEncodeBHist rightLower,
        realIntervalApartnessDecodeEncodeBHist rightUpper,
        realIntervalApartnessDecodeEncodeBHist gap,
        realIntervalApartnessDecodeEncodeBHist finiteWindow,
        realIntervalApartnessDecodeEncodeBHist readback,
        realIntervalApartnessDecodeEncodeBHist separability,
        realIntervalApartnessDecodeEncodeBHist transport,
        realIntervalApartnessDecodeEncodeBHist replay,
        realIntervalApartnessDecodeEncodeBHist provenance,
        realIntervalApartnessDecodeEncodeBHist nameCert]

private theorem realIntervalApartnessToEventFlow_injective {x y : RealIntervalApartnessUp} :
    realIntervalApartnessToEventFlow x = realIntervalApartnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalApartnessFromEventFlow (realIntervalApartnessToEventFlow x) =
        realIntervalApartnessFromEventFlow (realIntervalApartnessToEventFlow y) :=
    congrArg realIntervalApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realIntervalApartnessRoundTrip x).symm
      (Eq.trans hread (realIntervalApartnessRoundTrip y)))

private theorem realIntervalApartnessFields_faithful (x y : RealIntervalApartnessUp) :
    realIntervalApartnessFields x = realIntervalApartnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk leftInterval₁ rightInterval₁ leftLower₁ leftUpper₁ rightLower₁ rightUpper₁ gap₁
      finiteWindow₁ readback₁ separability₁ transport₁ replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk leftInterval₂ rightInterval₂ leftLower₂ leftUpper₂ rightLower₂ rightUpper₂ gap₂
          finiteWindow₂ readback₂ separability₂ transport₂ replay₂ provenance₂ nameCert₂ =>
          injection h with hLeftInterval hRest₁
          injection hRest₁ with hRightInterval hRest₂
          injection hRest₂ with hLeftLower hRest₃
          injection hRest₃ with hLeftUpper hRest₄
          injection hRest₄ with hRightLower hRest₅
          injection hRest₅ with hRightUpper hRest₆
          injection hRest₆ with hGap hRest₇
          injection hRest₇ with hFiniteWindow hRest₈
          injection hRest₈ with hReadback hRest₉
          injection hRest₉ with hSeparability hRest₁₀
          injection hRest₁₀ with hTransport hRest₁₁
          injection hRest₁₁ with hReplay hRest₁₂
          injection hRest₁₂ with hProvenance hRest₁₃
          injection hRest₁₃ with hNameCert _
          subst hLeftInterval
          subst hRightInterval
          subst hLeftLower
          subst hLeftUpper
          subst hRightLower
          subst hRightUpper
          subst hGap
          subst hFiniteWindow
          subst hReadback
          subst hSeparability
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hNameCert
          rfl

instance realIntervalApartnessBHistCarrier : BHistCarrier RealIntervalApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalApartnessToEventFlow
  fromEventFlow := realIntervalApartnessFromEventFlow

instance realIntervalApartnessChapterTasteGate : ChapterTasteGate RealIntervalApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalApartnessFromEventFlow (realIntervalApartnessToEventFlow x) = some x
    exact realIntervalApartnessRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realIntervalApartnessToEventFlow_injective heq)

instance realIntervalApartnessFieldFaithful : FieldFaithful RealIntervalApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realIntervalApartnessFields
  field_faithful := realIntervalApartnessFields_faithful

instance realIntervalApartnessNontrivial : Nontrivial RealIntervalApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealIntervalApartnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealIntervalApartnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealIntervalApartnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntervalApartnessChapterTasteGate

theorem RealIntervalApartnessTasteGate_single_carrier_alignment :
    (forall h : BHist, realIntervalApartnessDecodeBHist (realIntervalApartnessEncodeBHist h) = h) /\
      (forall x : RealIntervalApartnessUp,
        realIntervalApartnessFromEventFlow (realIntervalApartnessToEventFlow x) = some x) /\
      (forall x y : RealIntervalApartnessUp,
        realIntervalApartnessToEventFlow x = realIntervalApartnessToEventFlow y -> x = y) /\
      realIntervalApartnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realIntervalApartnessDecodeEncodeBHist
  · constructor
    · exact realIntervalApartnessRoundTrip
    · constructor
      · intro x y heq
        exact realIntervalApartnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealIntervalApartnessUp.TasteGate
