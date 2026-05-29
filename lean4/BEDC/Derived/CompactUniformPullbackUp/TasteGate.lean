import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# CompactUniformPullbackUp TasteGate carrier.
-/

namespace BEDC.Derived.CompactUniformPullbackUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Compact-uniform pullback packet with the eleven displayed rows. -/
inductive CompactUniformPullbackUp : Type where
  | mk :
      (compactMetric continuousMap uniformModulus dyadicTolerance regularReadback realSeal
        pullbackLedger transport replay provenance nameCert : BHist) →
      CompactUniformPullbackUp
  deriving DecidableEq

def compactUniformPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformPullbackEncodeBHist h

def compactUniformPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformPullbackDecodeBHist tail)

private theorem CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist, compactUniformPullbackDecodeBHist (compactUniformPullbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactUniformPullbackToEventFlow : CompactUniformPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformPullbackUp.mk compactMetric continuousMap uniformModulus dyadicTolerance
      regularReadback realSeal pullbackLedger transport replay provenance nameCert =>
      [[BMark.b0],
        compactUniformPullbackEncodeBHist compactMetric,
        [BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist continuousMap,
        [BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist uniformModulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist dyadicTolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist pullbackLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compactUniformPullbackEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactUniformPullbackEncodeBHist nameCert]

private def compactUniformPullbackDecodeRows : EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match compactUniformPullbackDecodeRows rest1 with
          | some rows => some (compactUniformPullbackDecodeBHist row :: rows)
          | none => none

private def compactUniformPullbackFromRows : List BHist → Option CompactUniformPullbackUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | compactMetric :: rest0 =>
      match rest0 with
      | [] => none
      | continuousMap :: rest1 =>
          match rest1 with
          | [] => none
          | uniformModulus :: rest2 =>
              match rest2 with
              | [] => none
              | dyadicTolerance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regularReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | pullbackLedger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | nameCert :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CompactUniformPullbackUp.mk
                                                      compactMetric continuousMap
                                                      uniformModulus dyadicTolerance
                                                      regularReadback realSeal
                                                      pullbackLedger transport replay
                                                      provenance nameCert)
                                              | _ :: _ => none

def compactUniformPullbackFromEventFlow : EventFlow → Option CompactUniformPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match compactUniformPullbackDecodeRows ef with
    | some rows => compactUniformPullbackFromRows rows
    | none => none

private theorem CompactUniformPullbackTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformPullbackUp,
      compactUniformPullbackFromEventFlow (compactUniformPullbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactMetric continuousMap uniformModulus dyadicTolerance regularReadback realSeal
      pullbackLedger transport replay provenance nameCert =>
      change
        some
          (CompactUniformPullbackUp.mk
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist compactMetric))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist continuousMap))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist uniformModulus))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist dyadicTolerance))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist regularReadback))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist realSeal))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist pullbackLedger))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist transport))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist replay))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist provenance))
            (compactUniformPullbackDecodeBHist
              (compactUniformPullbackEncodeBHist nameCert))) =
          some
            (CompactUniformPullbackUp.mk compactMetric continuousMap uniformModulus
              dyadicTolerance regularReadback realSeal pullbackLedger transport replay
              provenance nameCert)
      rw [CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
          compactMetric,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
          continuousMap,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
          uniformModulus,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
          dyadicTolerance,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
          regularReadback,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist realSeal,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
          pullbackLedger,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist transport,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist replay,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist provenance,
        CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist nameCert]

private theorem CompactUniformPullbackTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformPullbackUp} :
    compactUniformPullbackToEventFlow x = compactUniformPullbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformPullbackFromEventFlow (compactUniformPullbackToEventFlow x) =
        compactUniformPullbackFromEventFlow (compactUniformPullbackToEventFlow y) :=
    congrArg compactUniformPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactUniformPullbackTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompactUniformPullbackTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformPullbackBHistCarrier :
    BHistCarrier CompactUniformPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformPullbackToEventFlow
  fromEventFlow := compactUniformPullbackFromEventFlow

instance compactUniformPullbackChapterTasteGate :
    ChapterTasteGate CompactUniformPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformPullbackFromEventFlow (compactUniformPullbackToEventFlow x) = some x
    exact CompactUniformPullbackTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformPullbackTasteGate_single_carrier_alignment_toEventFlow_injective heq)

/-- Public TasteGate object for the compact-uniform pullback carrier. -/
def taste_gate : ChapterTasteGate CompactUniformPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformPullbackChapterTasteGate

theorem CompactUniformPullbackTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactUniformPullbackDecodeBHist (compactUniformPullbackEncodeBHist h) = h) ∧
      (∀ x : CompactUniformPullbackUp,
        compactUniformPullbackFromEventFlow (compactUniformPullbackToEventFlow x) = some x) ∧
      (∀ x y : CompactUniformPullbackUp,
        compactUniformPullbackToEventFlow x = compactUniformPullbackToEventFlow y → x = y) ∧
      compactUniformPullbackEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompactUniformPullbackTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact CompactUniformPullbackTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CompactUniformPullbackTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CompactUniformPullbackUp
