import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TrivialZeroClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TrivialZeroClassifierUp : Type where
  | mk :
      (I Q R Z E A H C P N : BHist) →
        TrivialZeroClassifierUp
  deriving DecidableEq

private def trivialZeroClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: trivialZeroClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: trivialZeroClassifierEncodeBHist h

private def trivialZeroClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (trivialZeroClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (trivialZeroClassifierDecodeBHist tail)

private theorem trivialZeroClassifierDecodeEncodeBHist :
    ∀ h : BHist,
      trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def trivialZeroClassifierToEventFlow : TrivialZeroClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TrivialZeroClassifierUp.mk I Q R Z E A H C P N =>
      [[BMark.b0],
        trivialZeroClassifierEncodeBHist I,
        [BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        trivialZeroClassifierEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        trivialZeroClassifierEncodeBHist N]

private def trivialZeroClassifierFromEventFlow :
    EventFlow → Option TrivialZeroClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
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
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Z :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | A :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (TrivialZeroClassifierUp.mk
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            I)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            Q)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            R)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            Z)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            E)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            A)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            H)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            C)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            P)
                                                                                          (trivialZeroClassifierDecodeBHist
                                                                                            N))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem trivialZeroClassifierRoundTrip :
    ∀ x : TrivialZeroClassifierUp,
      trivialZeroClassifierFromEventFlow (trivialZeroClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Q R Z E A H C P N =>
      change
        some
          (TrivialZeroClassifierUp.mk
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist I))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist Q))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist R))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist Z))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist E))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist A))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist H))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist C))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist P))
            (trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist N))) =
          some (TrivialZeroClassifierUp.mk I Q R Z E A H C P N)
      rw [trivialZeroClassifierDecodeEncodeBHist I,
        trivialZeroClassifierDecodeEncodeBHist Q,
        trivialZeroClassifierDecodeEncodeBHist R,
        trivialZeroClassifierDecodeEncodeBHist Z,
        trivialZeroClassifierDecodeEncodeBHist E,
        trivialZeroClassifierDecodeEncodeBHist A,
        trivialZeroClassifierDecodeEncodeBHist H,
        trivialZeroClassifierDecodeEncodeBHist C,
        trivialZeroClassifierDecodeEncodeBHist P,
        trivialZeroClassifierDecodeEncodeBHist N]

private theorem trivialZeroClassifierToEventFlow_injective
    {x y : TrivialZeroClassifierUp} :
    trivialZeroClassifierToEventFlow x = trivialZeroClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      trivialZeroClassifierFromEventFlow (trivialZeroClassifierToEventFlow x) =
        trivialZeroClassifierFromEventFlow (trivialZeroClassifierToEventFlow y) :=
    congrArg trivialZeroClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (trivialZeroClassifierRoundTrip x).symm
      (Eq.trans hread (trivialZeroClassifierRoundTrip y)))

private def trivialZeroClassifierFields : TrivialZeroClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TrivialZeroClassifierUp.mk I Q R Z E A H C P N => [I, Q, R, Z, E, A, H, C, P, N]

private theorem trivialZeroClassifierFields_faithful :
    ∀ x y : TrivialZeroClassifierUp,
      trivialZeroClassifierFields x = trivialZeroClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I₁ Q₁ R₁ Z₁ E₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ Q₂ R₂ Z₂ E₂ A₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance trivialZeroClassifierBHistCarrier : BHistCarrier TrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := trivialZeroClassifierToEventFlow
  fromEventFlow := trivialZeroClassifierFromEventFlow

instance trivialZeroClassifierChapterTasteGate :
    ChapterTasteGate TrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      trivialZeroClassifierFromEventFlow (trivialZeroClassifierToEventFlow x) = some x
    exact trivialZeroClassifierRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (trivialZeroClassifierToEventFlow_injective heq)

instance trivialZeroClassifierFieldFaithful :
    FieldFaithful TrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := trivialZeroClassifierFields
  field_faithful := trivialZeroClassifierFields_faithful

instance trivialZeroClassifierNontrivial :
    Nontrivial TrivialZeroClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TrivialZeroClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TrivialZeroClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TrivialZeroClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  trivialZeroClassifierChapterTasteGate

theorem TrivialZeroClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      trivialZeroClassifierDecodeBHist (trivialZeroClassifierEncodeBHist h) = h) ∧
      (∀ x : TrivialZeroClassifierUp,
        trivialZeroClassifierFromEventFlow (trivialZeroClassifierToEventFlow x) = some x) ∧
        (∀ x y : TrivialZeroClassifierUp,
          trivialZeroClassifierToEventFlow x = trivialZeroClassifierToEventFlow y → x = y) ∧
          trivialZeroClassifierEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : TrivialZeroClassifierUp,
              trivialZeroClassifierFields x = trivialZeroClassifierFields y → x = y) ∧
              (∃ x y : TrivialZeroClassifierUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact trivialZeroClassifierDecodeEncodeBHist
  · constructor
    · exact trivialZeroClassifierRoundTrip
    · constructor
      · intro x y heq
        exact trivialZeroClassifierToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact trivialZeroClassifierFields_faithful
          · exact
              ⟨TrivialZeroClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                TrivialZeroClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.TrivialZeroClassifierUp
