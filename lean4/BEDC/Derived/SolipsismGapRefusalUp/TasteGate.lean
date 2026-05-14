import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SolipsismGapRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SolipsismGapRefusalUp : Type where
  | mk : (E R G H C P N : BHist) → SolipsismGapRefusalUp
  deriving DecidableEq

def solipsismGapRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: solipsismGapRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: solipsismGapRefusalEncodeBHist h

def solipsismGapRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (solipsismGapRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (solipsismGapRefusalDecodeBHist tail)

private theorem solipsismGapRefusalDecode_encode_bhist :
    ∀ h : BHist, solipsismGapRefusalDecodeBHist
      (solipsismGapRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def solipsismGapRefusalToEventFlow : SolipsismGapRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SolipsismGapRefusalUp.mk E R G H C P N =>
      [[BMark.b0],
        solipsismGapRefusalEncodeBHist E,
        [BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        solipsismGapRefusalEncodeBHist N]

def solipsismGapRefusalFromEventFlow : EventFlow → Option SolipsismGapRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (SolipsismGapRefusalUp.mk
                                                                  (solipsismGapRefusalDecodeBHist E)
                                                                  (solipsismGapRefusalDecodeBHist R)
                                                                  (solipsismGapRefusalDecodeBHist G)
                                                                  (solipsismGapRefusalDecodeBHist H)
                                                                  (solipsismGapRefusalDecodeBHist C)
                                                                  (solipsismGapRefusalDecodeBHist P)
                                                                  (solipsismGapRefusalDecodeBHist N))
                                                          | _ :: _ => none

private theorem solipsismGapRefusal_round_trip :
    ∀ x : SolipsismGapRefusalUp,
      solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E R G H C P N =>
      change
        some
          (SolipsismGapRefusalUp.mk
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist E))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist R))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist G))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist H))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist C))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist P))
            (solipsismGapRefusalDecodeBHist (solipsismGapRefusalEncodeBHist N))) =
          some (SolipsismGapRefusalUp.mk E R G H C P N)
      rw [solipsismGapRefusalDecode_encode_bhist E,
        solipsismGapRefusalDecode_encode_bhist R,
        solipsismGapRefusalDecode_encode_bhist G,
        solipsismGapRefusalDecode_encode_bhist H,
        solipsismGapRefusalDecode_encode_bhist C,
        solipsismGapRefusalDecode_encode_bhist P,
        solipsismGapRefusalDecode_encode_bhist N]

private theorem solipsismGapRefusalToEventFlow_injective {x y : SolipsismGapRefusalUp} :
    solipsismGapRefusalToEventFlow x = solipsismGapRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) =
        solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow y) :=
    congrArg solipsismGapRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (solipsismGapRefusal_round_trip x).symm
      (Eq.trans hread (solipsismGapRefusal_round_trip y)))

instance solipsismGapRefusalBHistCarrier : BHistCarrier SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := solipsismGapRefusalToEventFlow
  fromEventFlow := solipsismGapRefusalFromEventFlow

instance solipsismGapRefusalChapterTasteGate : ChapterTasteGate SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x
    exact solipsismGapRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (solipsismGapRefusalToEventFlow_injective heq)

instance solipsismGapRefusalFieldFaithful : FieldFaithful SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SolipsismGapRefusalUp.mk E R G H C P N => [E, R, G, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk E1 R1 G1 H1 C1 P1 N1 =>
        cases y with
        | mk E2 R2 G2 H2 C2 P2 N2 =>
            cases h
            rfl

instance solipsismGapRefusalNontrivial : Nontrivial SolipsismGapRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SolipsismGapRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      SolipsismGapRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SolipsismGapRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  solipsismGapRefusalChapterTasteGate

theorem SolipsismGapRefusalTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SolipsismGapRefusalUp) ∧
      (∀ x : SolipsismGapRefusalUp,
        solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x) ∧
      (∀ x y : SolipsismGapRefusalUp,
        solipsismGapRefusalToEventFlow x = solipsismGapRefusalToEventFlow y → x = y) ∧
      solipsismGapRefusalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨solipsismGapRefusalChapterTasteGate⟩
  · constructor
    · intro x
      change solipsismGapRefusalFromEventFlow (solipsismGapRefusalToEventFlow x) = some x
      exact solipsismGapRefusal_round_trip x
    · constructor
      · intro x y heq
        exact solipsismGapRefusalToEventFlow_injective heq
      · rfl

end BEDC.Derived.SolipsismGapRefusalUp
