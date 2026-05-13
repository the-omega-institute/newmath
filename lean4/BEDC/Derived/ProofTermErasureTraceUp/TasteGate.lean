import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofTermErasureTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofTermErasureTraceUp : Type where
  | mk :
      (p e T E R H C P N : BHist) →
        ProofTermErasureTraceUp
  deriving DecidableEq

def proofTermErasureTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofTermErasureTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofTermErasureTraceEncodeBHist h

def proofTermErasureTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofTermErasureTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofTermErasureTraceDecodeBHist tail)

private theorem proofTermErasureTraceDecodeEncodeBHist :
    ∀ h : BHist,
      proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def proofTermErasureTraceToEventFlow : ProofTermErasureTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofTermErasureTraceUp.mk p e T E R H C P N =>
      [[BMark.b0],
        proofTermErasureTraceEncodeBHist p,
        [BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        proofTermErasureTraceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        proofTermErasureTraceEncodeBHist N]

def proofTermErasureTraceFromEventFlow :
    EventFlow → Option ProofTermErasureTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | p :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | e :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ProofTermErasureTraceUp.mk
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    p)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    e)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    T)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    E)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    R)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    H)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    C)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    P)
                                                                                  (proofTermErasureTraceDecodeBHist
                                                                                    N))
                                                                          | _ :: _ =>
                                                                              none

private theorem proofTermErasureTraceRoundTrip :
    ∀ x : ProofTermErasureTraceUp,
      proofTermErasureTraceFromEventFlow (proofTermErasureTraceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p e T E R H C P N =>
      change
        some
          (ProofTermErasureTraceUp.mk
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist p))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist e))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist T))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist E))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist R))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist H))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist C))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist P))
            (proofTermErasureTraceDecodeBHist (proofTermErasureTraceEncodeBHist N))) =
          some (ProofTermErasureTraceUp.mk p e T E R H C P N)
      rw [proofTermErasureTraceDecodeEncodeBHist p,
        proofTermErasureTraceDecodeEncodeBHist e,
        proofTermErasureTraceDecodeEncodeBHist T,
        proofTermErasureTraceDecodeEncodeBHist E,
        proofTermErasureTraceDecodeEncodeBHist R,
        proofTermErasureTraceDecodeEncodeBHist H,
        proofTermErasureTraceDecodeEncodeBHist C,
        proofTermErasureTraceDecodeEncodeBHist P,
        proofTermErasureTraceDecodeEncodeBHist N]

private theorem proofTermErasureTraceToEventFlow_injective
    {x y : ProofTermErasureTraceUp} :
    proofTermErasureTraceToEventFlow x = proofTermErasureTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofTermErasureTraceFromEventFlow (proofTermErasureTraceToEventFlow x) =
        proofTermErasureTraceFromEventFlow (proofTermErasureTraceToEventFlow y) :=
    congrArg proofTermErasureTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (proofTermErasureTraceRoundTrip x).symm
      (Eq.trans hread (proofTermErasureTraceRoundTrip y)))

instance proofTermErasureTraceBHistCarrier : BHistCarrier ProofTermErasureTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofTermErasureTraceToEventFlow
  fromEventFlow := proofTermErasureTraceFromEventFlow

instance proofTermErasureTraceChapterTasteGate :
    ChapterTasteGate ProofTermErasureTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proofTermErasureTraceFromEventFlow (proofTermErasureTraceToEventFlow x) = some x
    exact proofTermErasureTraceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proofTermErasureTraceToEventFlow_injective heq)

theorem ProofTermErasureTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, proofTermErasureTraceDecodeBHist
        (proofTermErasureTraceEncodeBHist h) = h) ∧
      (∀ x : ProofTermErasureTraceUp,
        proofTermErasureTraceFromEventFlow (proofTermErasureTraceToEventFlow x) =
          some x) ∧
        (∀ x y : ProofTermErasureTraceUp,
          proofTermErasureTraceToEventFlow x = proofTermErasureTraceToEventFlow y →
            x = y) ∧
          proofTermErasureTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact proofTermErasureTraceDecodeEncodeBHist
  · constructor
    · intro x
      exact proofTermErasureTraceRoundTrip x
    · constructor
      · intro x y heq
        exact proofTermErasureTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.ProofTermErasureTraceUp
