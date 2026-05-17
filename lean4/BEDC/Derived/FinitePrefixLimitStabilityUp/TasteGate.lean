import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixLimitStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixLimitStabilityUp : Type where
  | mk
      (budget window readback tolerance realSeal transport replay provenance localName : BHist) :
      FinitePrefixLimitStabilityUp
  deriving DecidableEq

def finitePrefixLimitStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixLimitStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixLimitStabilityEncodeBHist h

def finitePrefixLimitStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixLimitStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixLimitStabilityDecodeBHist tail)

private theorem finitePrefixLimitStability_decode_encode_bhist :
    ∀ h : BHist,
      finitePrefixLimitStabilityDecodeBHist (finitePrefixLimitStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finitePrefixLimitStabilityToEventFlow : FinitePrefixLimitStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixLimitStabilityUp.mk budget window readback tolerance realSeal transport replay
      provenance localName =>
      [[BMark.b0],
        finitePrefixLimitStabilityEncodeBHist budget,
        [BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finitePrefixLimitStabilityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finitePrefixLimitStabilityEncodeBHist localName]

def finitePrefixLimitStabilityFromEventFlow :
    EventFlow → Option FinitePrefixLimitStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | budget :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tolerance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
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
                                                                                (FinitePrefixLimitStabilityUp.mk
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    budget)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    window)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    readback)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    tolerance)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    realSeal)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    transport)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    replay)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    provenance)
                                                                                  (finitePrefixLimitStabilityDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem finitePrefixLimitStability_round_trip :
    ∀ x : FinitePrefixLimitStabilityUp,
      finitePrefixLimitStabilityFromEventFlow
          (finitePrefixLimitStabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk budget window readback tolerance realSeal transport replay provenance localName =>
      change
        some
          (FinitePrefixLimitStabilityUp.mk
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist budget))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist window))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist readback))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist tolerance))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist realSeal))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist transport))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist replay))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist provenance))
            (finitePrefixLimitStabilityDecodeBHist
              (finitePrefixLimitStabilityEncodeBHist localName))) =
          some
            (FinitePrefixLimitStabilityUp.mk budget window readback tolerance realSeal transport
              replay provenance localName)
      rw [finitePrefixLimitStability_decode_encode_bhist budget,
        finitePrefixLimitStability_decode_encode_bhist window,
        finitePrefixLimitStability_decode_encode_bhist readback,
        finitePrefixLimitStability_decode_encode_bhist tolerance,
        finitePrefixLimitStability_decode_encode_bhist realSeal,
        finitePrefixLimitStability_decode_encode_bhist transport,
        finitePrefixLimitStability_decode_encode_bhist replay,
        finitePrefixLimitStability_decode_encode_bhist provenance,
        finitePrefixLimitStability_decode_encode_bhist localName]

private theorem finitePrefixLimitStabilityToEventFlow_injective
    {x y : FinitePrefixLimitStabilityUp} :
    finitePrefixLimitStabilityToEventFlow x =
      finitePrefixLimitStabilityToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixLimitStabilityFromEventFlow (finitePrefixLimitStabilityToEventFlow x) =
        finitePrefixLimitStabilityFromEventFlow (finitePrefixLimitStabilityToEventFlow y) :=
    congrArg finitePrefixLimitStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finitePrefixLimitStability_round_trip x).symm
      (Eq.trans hread (finitePrefixLimitStability_round_trip y)))

instance finitePrefixLimitStabilityBHistCarrier :
    BHistCarrier FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixLimitStabilityToEventFlow
  fromEventFlow := finitePrefixLimitStabilityFromEventFlow

instance finitePrefixLimitStabilityChapterTasteGate :
    ChapterTasteGate FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finitePrefixLimitStabilityFromEventFlow (finitePrefixLimitStabilityToEventFlow x) =
        some x
    exact finitePrefixLimitStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finitePrefixLimitStabilityToEventFlow_injective heq)

instance finitePrefixLimitStabilityFieldFaithful :
    FieldFaithful FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FinitePrefixLimitStabilityUp.mk budget window readback tolerance realSeal transport replay
        provenance localName =>
        [budget, window, readback, tolerance, realSeal, transport, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk budget₁ window₁ readback₁ tolerance₁ realSeal₁ transport₁ replay₁ provenance₁
        localName₁ =>
        cases y with
        | mk budget₂ window₂ readback₂ tolerance₂ realSeal₂ transport₂ replay₂ provenance₂
            localName₂ =>
            simp only [] at h
            cases h
            rfl

instance finitePrefixLimitStabilityNontrivial :
    Nontrivial FinitePrefixLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePrefixLimitStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FinitePrefixLimitStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FinitePrefixLimitStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finitePrefixLimitStabilityChapterTasteGate

theorem FinitePrefixLimitStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finitePrefixLimitStabilityDecodeBHist (finitePrefixLimitStabilityEncodeBHist h) = h) ∧
      (∀ x : FinitePrefixLimitStabilityUp,
        finitePrefixLimitStabilityFromEventFlow
            (finitePrefixLimitStabilityToEventFlow x) =
          some x) ∧
        (∀ x y : FinitePrefixLimitStabilityUp,
          finitePrefixLimitStabilityToEventFlow x =
              finitePrefixLimitStabilityToEventFlow y →
            x = y) ∧
          Nonempty (FieldFaithful FinitePrefixLimitStabilityUp) ∧
            Nonempty (ChapterTasteGate FinitePrefixLimitStabilityUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finitePrefixLimitStability_decode_encode_bhist
  · constructor
    · exact finitePrefixLimitStability_round_trip
    · constructor
      · intro x y heq
        exact finitePrefixLimitStabilityToEventFlow_injective heq
      · constructor
        · exact Nonempty.intro finitePrefixLimitStabilityFieldFaithful
        · exact Nonempty.intro finitePrefixLimitStabilityChapterTasteGate

end BEDC.Derived.FinitePrefixLimitStabilityUp
