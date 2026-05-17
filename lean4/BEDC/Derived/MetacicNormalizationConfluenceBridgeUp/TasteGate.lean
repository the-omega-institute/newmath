import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicNormalizationConfluenceBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicNormalizationConfluenceBridgeUp : Type where
  | mk (N Q D A T H C P L : BHist) : MetacicNormalizationConfluenceBridgeUp
  deriving DecidableEq

def metacicNormalizationConfluenceBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicNormalizationConfluenceBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicNormalizationConfluenceBridgeEncodeBHist h

def metacicNormalizationConfluenceBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicNormalizationConfluenceBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicNormalizationConfluenceBridgeDecodeBHist tail)

private theorem metacicNormalizationConfluenceBridgeDecode_encode_bhist :
    ∀ h : BHist,
      metacicNormalizationConfluenceBridgeDecodeBHist
        (metacicNormalizationConfluenceBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicNormalizationConfluenceBridgeToEventFlow :
    MetacicNormalizationConfluenceBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicNormalizationConfluenceBridgeUp.mk N Q D A T H C P L =>
      [[BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist N,
        [BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicNormalizationConfluenceBridgeEncodeBHist L]

def metacicNormalizationConfluenceBridgeFromEventFlow :
    EventFlow → Option MetacicNormalizationConfluenceBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | N :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | A :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | T :: rest9 =>
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
                                                                      | L :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetacicNormalizationConfluenceBridgeUp.mk
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    N)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    Q)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    D)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    A)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    T)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    H)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    C)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    P)
                                                                                  (metacicNormalizationConfluenceBridgeDecodeBHist
                                                                                    L))
                                                                          | _ :: _ => none

private theorem metacicNormalizationConfluenceBridge_round_trip :
    ∀ x : MetacicNormalizationConfluenceBridgeUp,
      metacicNormalizationConfluenceBridgeFromEventFlow
        (metacicNormalizationConfluenceBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N Q D A T H C P L =>
      change
        some
          (MetacicNormalizationConfluenceBridgeUp.mk
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist N))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist Q))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist D))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist A))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist T))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist H))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist C))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist P))
            (metacicNormalizationConfluenceBridgeDecodeBHist
              (metacicNormalizationConfluenceBridgeEncodeBHist L))) =
          some (MetacicNormalizationConfluenceBridgeUp.mk N Q D A T H C P L)
      rw [metacicNormalizationConfluenceBridgeDecode_encode_bhist N,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist Q,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist D,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist A,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist T,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist H,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist C,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist P,
        metacicNormalizationConfluenceBridgeDecode_encode_bhist L]

private theorem metacicNormalizationConfluenceBridgeToEventFlow_injective
    {x y : MetacicNormalizationConfluenceBridgeUp} :
    metacicNormalizationConfluenceBridgeToEventFlow x =
      metacicNormalizationConfluenceBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicNormalizationConfluenceBridgeFromEventFlow
          (metacicNormalizationConfluenceBridgeToEventFlow x) =
        metacicNormalizationConfluenceBridgeFromEventFlow
          (metacicNormalizationConfluenceBridgeToEventFlow y) :=
    congrArg metacicNormalizationConfluenceBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicNormalizationConfluenceBridge_round_trip x).symm
      (Eq.trans hread (metacicNormalizationConfluenceBridge_round_trip y)))

instance metacicNormalizationConfluenceBridgeBHistCarrier :
    BHistCarrier MetacicNormalizationConfluenceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicNormalizationConfluenceBridgeToEventFlow
  fromEventFlow := metacicNormalizationConfluenceBridgeFromEventFlow

instance metacicNormalizationConfluenceBridgeChapterTasteGate :
    ChapterTasteGate MetacicNormalizationConfluenceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicNormalizationConfluenceBridgeFromEventFlow
        (metacicNormalizationConfluenceBridgeToEventFlow x) = some x
    exact metacicNormalizationConfluenceBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicNormalizationConfluenceBridgeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetacicNormalizationConfluenceBridgeUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact metacicNormalizationConfluenceBridgeChapterTasteGate

def metacicNormalizationConfluenceBridgeFields :
    MetacicNormalizationConfluenceBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicNormalizationConfluenceBridgeUp.mk N Q D A T H C P L =>
      [N, Q, D, A, T, H, C, P, L]

instance metacicNormalizationConfluenceBridgeFieldFaithful :
    FieldFaithful MetacicNormalizationConfluenceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicNormalizationConfluenceBridgeFields
  field_faithful := by
    intro x y h
    cases x with
    | mk N₁ Q₁ D₁ A₁ T₁ H₁ C₁ P₁ L₁ =>
        cases y with
        | mk N₂ Q₂ D₂ A₂ T₂ H₂ C₂ P₂ L₂ =>
            cases h
            rfl

instance metacicNormalizationConfluenceBridgeNontrivial :
    Nontrivial MetacicNormalizationConfluenceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetacicNormalizationConfluenceBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetacicNormalizationConfluenceBridgeUp.mk BHist.Empty BHist.Empty
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetacicNormalizationConfluenceBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicNormalizationConfluenceBridgeDecodeBHist
        (metacicNormalizationConfluenceBridgeEncodeBHist h) = h) ∧
      (∀ x : MetacicNormalizationConfluenceBridgeUp,
        metacicNormalizationConfluenceBridgeFromEventFlow
          (metacicNormalizationConfluenceBridgeToEventFlow x) = some x) ∧
        (∀ x y : MetacicNormalizationConfluenceBridgeUp,
          metacicNormalizationConfluenceBridgeToEventFlow x =
              metacicNormalizationConfluenceBridgeToEventFlow y →
            x = y) ∧
          metacicNormalizationConfluenceBridgeEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : MetacicNormalizationConfluenceBridgeUp,
              metacicNormalizationConfluenceBridgeFields x =
                  metacicNormalizationConfluenceBridgeFields y →
                x = y) ∧
              (∃ x y : MetacicNormalizationConfluenceBridgeUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicNormalizationConfluenceBridgeDecode_encode_bhist
  · constructor
    · exact metacicNormalizationConfluenceBridge_round_trip
    · constructor
      · intro x y heq
        exact metacicNormalizationConfluenceBridgeToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · intro x y h
            exact FieldFaithful.field_faithful x y h
          · exact
              ⟨MetacicNormalizationConfluenceBridgeUp.mk BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                MetacicNormalizationConfluenceBridgeUp.mk BHist.Empty BHist.Empty
                  (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.MetacicNormalizationConfluenceBridgeUp
