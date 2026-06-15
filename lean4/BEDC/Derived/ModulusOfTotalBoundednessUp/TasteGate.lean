import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusOfTotalBoundednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusOfTotalBoundednessUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk
      (metric tolerance window totalBounded centers coverage transport replay provenance name :
        BHist) : ModulusOfTotalBoundednessUp
  deriving DecidableEq

def modulusOfTotalBoundednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusOfTotalBoundednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusOfTotalBoundednessEncodeBHist h

def modulusOfTotalBoundednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusOfTotalBoundednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusOfTotalBoundednessDecodeBHist tail)

private theorem modulusOfTotalBoundednessDecodeEncode :
    ∀ h : BHist,
      modulusOfTotalBoundednessDecodeBHist (modulusOfTotalBoundednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def modulusOfTotalBoundednessFields : ModulusOfTotalBoundednessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfTotalBoundednessUp.mk metric tolerance window totalBounded centers coverage
      transport replay provenance name =>
      [metric, tolerance, window, totalBounded, centers, coverage, transport, replay,
        provenance, name]

def modulusOfTotalBoundednessToEventFlow : ModulusOfTotalBoundednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (modulusOfTotalBoundednessFields x).map modulusOfTotalBoundednessEncodeBHist

def modulusOfTotalBoundednessFromEventFlow :
    EventFlow → Option ModulusOfTotalBoundednessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | metric :: rest0 =>
      match rest0 with
      | [] => none
      | tolerance :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | totalBounded :: rest3 =>
                  match rest3 with
                  | [] => none
                  | centers :: rest4 =>
                      match rest4 with
                      | [] => none
                      | coverage :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ModulusOfTotalBoundednessUp.mk
                                                  (modulusOfTotalBoundednessDecodeBHist metric)
                                                  (modulusOfTotalBoundednessDecodeBHist
                                                    tolerance)
                                                  (modulusOfTotalBoundednessDecodeBHist window)
                                                  (modulusOfTotalBoundednessDecodeBHist
                                                    totalBounded)
                                                  (modulusOfTotalBoundednessDecodeBHist
                                                    centers)
                                                  (modulusOfTotalBoundednessDecodeBHist
                                                    coverage)
                                                  (modulusOfTotalBoundednessDecodeBHist
                                                    transport)
                                                  (modulusOfTotalBoundednessDecodeBHist replay)
                                                  (modulusOfTotalBoundednessDecodeBHist
                                                    provenance)
                                                  (modulusOfTotalBoundednessDecodeBHist name))
                                          | _ :: _ => none

private theorem modulusOfTotalBoundednessRoundTrip (x : ModulusOfTotalBoundednessUp) :
    modulusOfTotalBoundednessFromEventFlow (modulusOfTotalBoundednessToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk metric tolerance window totalBounded centers coverage transport replay provenance name =>
      change
        some
          (ModulusOfTotalBoundednessUp.mk
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist metric))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist tolerance))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist window))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist totalBounded))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist centers))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist coverage))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist transport))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist replay))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist provenance))
            (modulusOfTotalBoundednessDecodeBHist
              (modulusOfTotalBoundednessEncodeBHist name))) =
          some
            (ModulusOfTotalBoundednessUp.mk metric tolerance window totalBounded centers
              coverage transport replay provenance name)
      rw [modulusOfTotalBoundednessDecodeEncode metric,
        modulusOfTotalBoundednessDecodeEncode tolerance,
        modulusOfTotalBoundednessDecodeEncode window,
        modulusOfTotalBoundednessDecodeEncode totalBounded,
        modulusOfTotalBoundednessDecodeEncode centers,
        modulusOfTotalBoundednessDecodeEncode coverage,
        modulusOfTotalBoundednessDecodeEncode transport,
        modulusOfTotalBoundednessDecodeEncode replay,
        modulusOfTotalBoundednessDecodeEncode provenance,
        modulusOfTotalBoundednessDecodeEncode name]

private theorem modulusOfTotalBoundednessToEventFlow_injective
    {x y : ModulusOfTotalBoundednessUp} :
    modulusOfTotalBoundednessToEventFlow x = modulusOfTotalBoundednessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusOfTotalBoundednessFromEventFlow (modulusOfTotalBoundednessToEventFlow x) =
        modulusOfTotalBoundednessFromEventFlow (modulusOfTotalBoundednessToEventFlow y) :=
    congrArg modulusOfTotalBoundednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modulusOfTotalBoundednessRoundTrip x).symm
      (Eq.trans hread (modulusOfTotalBoundednessRoundTrip y)))

private theorem modulusOfTotalBoundednessFields_faithful :
    ∀ x y : ModulusOfTotalBoundednessUp,
      modulusOfTotalBoundednessFields x = modulusOfTotalBoundednessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric₁ tolerance₁ window₁ totalBounded₁ centers₁ coverage₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk metric₂ tolerance₂ window₂ totalBounded₂ centers₂ coverage₂ transport₂ replay₂
          provenance₂ name₂ =>
          injection hfields with hMetric tail0
          injection tail0 with hTolerance tail1
          injection tail1 with hWindow tail2
          injection tail2 with hTotalBounded tail3
          injection tail3 with hCenters tail4
          injection tail4 with hCoverage tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hName _
          subst hMetric
          subst hTolerance
          subst hWindow
          subst hTotalBounded
          subst hCenters
          subst hCoverage
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance modulusOfTotalBoundednessBHistCarrier :
    BHistCarrier ModulusOfTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusOfTotalBoundednessToEventFlow
  fromEventFlow := modulusOfTotalBoundednessFromEventFlow

instance modulusOfTotalBoundednessChapterTasteGate :
    ChapterTasteGate ModulusOfTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := modulusOfTotalBoundednessRoundTrip
  layer_separation := by
    intro x y hxy heq
    exact hxy (modulusOfTotalBoundednessToEventFlow_injective heq)

instance modulusOfTotalBoundednessFieldFaithful :
    FieldFaithful ModulusOfTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modulusOfTotalBoundednessFields
  field_faithful := modulusOfTotalBoundednessFields_faithful

instance modulusOfTotalBoundednessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ModulusOfTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModulusOfTotalBoundednessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModulusOfTotalBoundednessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hMetric
        cases hMetric⟩

def taste_gate : ChapterTasteGate ModulusOfTotalBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := modulusOfTotalBoundednessRoundTrip
  layer_separation := by
    intro x y hxy heq
    exact hxy (modulusOfTotalBoundednessToEventFlow_injective heq)

theorem ModulusOfTotalBoundednessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      modulusOfTotalBoundednessDecodeBHist (modulusOfTotalBoundednessEncodeBHist h) = h) ∧
      (∀ x : ModulusOfTotalBoundednessUp,
        modulusOfTotalBoundednessFromEventFlow
            (modulusOfTotalBoundednessToEventFlow x) =
          some x) ∧
        (∀ x y : ModulusOfTotalBoundednessUp,
          modulusOfTotalBoundednessToEventFlow x =
              modulusOfTotalBoundednessToEventFlow y →
            x = y) ∧
          modulusOfTotalBoundednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact modulusOfTotalBoundednessDecodeEncode
  · constructor
    · exact modulusOfTotalBoundednessRoundTrip
    · constructor
      · intro x y heq
        exact modulusOfTotalBoundednessToEventFlow_injective heq
      · rfl

end BEDC.Derived.ModulusOfTotalBoundednessUp
