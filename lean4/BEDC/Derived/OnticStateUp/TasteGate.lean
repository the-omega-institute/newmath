import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticStateUp : Type where
  | mk : (S A K R H C P N : BHist) → OnticStateUp
  deriving DecidableEq

def onticStateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticStateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticStateEncodeBHist h

def onticStateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticStateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticStateDecodeBHist tail)

private theorem onticStateDecode_encode_bhist :
    ∀ h : BHist, onticStateDecodeBHist (onticStateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def onticStateToEventFlow : OnticStateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OnticStateUp.mk S A K R H C P N =>
      [[BMark.b0],
        onticStateEncodeBHist S,
        [BMark.b1, BMark.b0],
        onticStateEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        onticStateEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        onticStateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        onticStateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        onticStateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        onticStateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        onticStateEncodeBHist N]

def onticStateFromEventFlow : EventFlow → Option OnticStateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (OnticStateUp.mk
                                                                          (onticStateDecodeBHist S)
                                                                          (onticStateDecodeBHist A)
                                                                          (onticStateDecodeBHist K)
                                                                          (onticStateDecodeBHist R)
                                                                          (onticStateDecodeBHist H)
                                                                          (onticStateDecodeBHist C)
                                                                          (onticStateDecodeBHist P)
                                                                          (onticStateDecodeBHist N))
                                                                  | _ :: _ => none

private theorem onticState_round_trip :
    ∀ x : OnticStateUp, onticStateFromEventFlow (onticStateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A K R H C P N =>
      change
        some
          (OnticStateUp.mk
            (onticStateDecodeBHist (onticStateEncodeBHist S))
            (onticStateDecodeBHist (onticStateEncodeBHist A))
            (onticStateDecodeBHist (onticStateEncodeBHist K))
            (onticStateDecodeBHist (onticStateEncodeBHist R))
            (onticStateDecodeBHist (onticStateEncodeBHist H))
            (onticStateDecodeBHist (onticStateEncodeBHist C))
            (onticStateDecodeBHist (onticStateEncodeBHist P))
            (onticStateDecodeBHist (onticStateEncodeBHist N))) =
          some (OnticStateUp.mk S A K R H C P N)
      rw [onticStateDecode_encode_bhist S, onticStateDecode_encode_bhist A,
        onticStateDecode_encode_bhist K, onticStateDecode_encode_bhist R,
        onticStateDecode_encode_bhist H, onticStateDecode_encode_bhist C,
        onticStateDecode_encode_bhist P, onticStateDecode_encode_bhist N]

theorem onticStateToEventFlow_injective {x y : OnticStateUp} :
    onticStateToEventFlow x = onticStateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticStateFromEventFlow (onticStateToEventFlow x) =
        onticStateFromEventFlow (onticStateToEventFlow y) :=
    congrArg onticStateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticState_round_trip x).symm (Eq.trans hread (onticState_round_trip y)))

instance onticStateBHistCarrier : BHistCarrier OnticStateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticStateToEventFlow
  fromEventFlow := onticStateFromEventFlow

instance onticStateChapterTasteGate : ChapterTasteGate OnticStateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticStateFromEventFlow (onticStateToEventFlow x) = some x
    exact onticState_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticStateToEventFlow_injective heq)

instance onticStateFieldFaithful : FieldFaithful OnticStateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | OnticStateUp.mk S A K R H C P N => [S, A, K, R, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ A₁ K₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S₂ A₂ K₂ R₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance onticStateNontrivial : Nontrivial OnticStateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticStateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      OnticStateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OnticStateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onticStateChapterTasteGate

theorem OnticStateTasteGate_single_carrier_alignment :
    (∀ h : BHist, onticStateDecodeBHist (onticStateEncodeBHist h) = h) ∧
      (∀ x : OnticStateUp, onticStateFromEventFlow (onticStateToEventFlow x) = some x) ∧
        (∀ x y : OnticStateUp, onticStateToEventFlow x = onticStateToEventFlow y → x = y) ∧
          onticStateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact onticStateDecode_encode_bhist
  · constructor
    · exact onticState_round_trip
    · constructor
      · intro x y heq
        exact onticStateToEventFlow_injective heq
      · rfl

theorem onticStateTasteGate_single_carrier_alignment :
    (∀ h : BHist, onticStateDecodeBHist (onticStateEncodeBHist h) = h) ∧
      (∀ x : OnticStateUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (∀ x y : OnticStateUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) ∧
          BHistCarrier.toEventFlow
              (OnticStateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty) ≠
            BHistCarrier.toEventFlow
              (OnticStateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact onticStateDecode_encode_bhist
  constructor
  · intro x
    change onticStateFromEventFlow (onticStateToEventFlow x) = some x
    exact onticState_round_trip x
  constructor
  · intro x y heq
    change onticStateToEventFlow x = onticStateToEventFlow y at heq
    exact onticStateToEventFlow_injective heq
  · intro heq
    change onticStateToEventFlow
          (OnticStateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        onticStateToEventFlow
          (OnticStateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) at heq
    cases heq

end BEDC.Derived.OnticStateUp
