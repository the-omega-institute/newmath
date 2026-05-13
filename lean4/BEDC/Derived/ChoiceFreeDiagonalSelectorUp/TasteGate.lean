import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoiceFreeDiagonalSelectorUp : Type where
  | mk :
      (request window observations witness sealRow transports routes provenance nameCert : BHist) →
        ChoiceFreeDiagonalSelectorUp
  deriving DecidableEq

def choiceFreeDiagonalSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choiceFreeDiagonalSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choiceFreeDiagonalSelectorEncodeBHist h

def choiceFreeDiagonalSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choiceFreeDiagonalSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choiceFreeDiagonalSelectorDecodeBHist tail)

private theorem choiceFreeDiagonalSelectorDecodeEncodeBHist :
    ∀ h : BHist,
      choiceFreeDiagonalSelectorDecodeBHist
        (choiceFreeDiagonalSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def choiceFreeDiagonalSelectorToEventFlow :
    ChoiceFreeDiagonalSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChoiceFreeDiagonalSelectorUp.mk request window observations witness sealRow transports
      routes provenance nameCert =>
      [[BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist request,
        [BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist observations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        choiceFreeDiagonalSelectorEncodeBHist nameCert]

def choiceFreeDiagonalSelectorFromEventFlow :
    EventFlow → Option ChoiceFreeDiagonalSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
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
                      | observations :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | witness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
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
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              some
                                                                                (ChoiceFreeDiagonalSelectorUp.mk
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    request)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    window)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    observations)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    witness)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    sealRow)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    transports)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    routes)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    provenance)
                                                                                  (choiceFreeDiagonalSelectorDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ =>
                                                                              none

private theorem choiceFreeDiagonalSelectorRoundTrip :
    ∀ x : ChoiceFreeDiagonalSelectorUp,
      choiceFreeDiagonalSelectorFromEventFlow
        (choiceFreeDiagonalSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request window observations witness sealRow transports routes provenance nameCert =>
      change
        some
          (ChoiceFreeDiagonalSelectorUp.mk
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist request))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist window))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist observations))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist witness))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist sealRow))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist transports))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist routes))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist provenance))
            (choiceFreeDiagonalSelectorDecodeBHist
              (choiceFreeDiagonalSelectorEncodeBHist nameCert))) =
          some
            (ChoiceFreeDiagonalSelectorUp.mk request window observations witness sealRow
              transports routes provenance nameCert)
      rw [choiceFreeDiagonalSelectorDecodeEncodeBHist request,
        choiceFreeDiagonalSelectorDecodeEncodeBHist window,
        choiceFreeDiagonalSelectorDecodeEncodeBHist observations,
        choiceFreeDiagonalSelectorDecodeEncodeBHist witness,
        choiceFreeDiagonalSelectorDecodeEncodeBHist sealRow,
        choiceFreeDiagonalSelectorDecodeEncodeBHist transports,
        choiceFreeDiagonalSelectorDecodeEncodeBHist routes,
        choiceFreeDiagonalSelectorDecodeEncodeBHist provenance,
        choiceFreeDiagonalSelectorDecodeEncodeBHist nameCert]

private theorem choiceFreeDiagonalSelectorToEventFlow_injective
    {x y : ChoiceFreeDiagonalSelectorUp} :
    choiceFreeDiagonalSelectorToEventFlow x =
      choiceFreeDiagonalSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choiceFreeDiagonalSelectorFromEventFlow
          (choiceFreeDiagonalSelectorToEventFlow x) =
        choiceFreeDiagonalSelectorFromEventFlow
          (choiceFreeDiagonalSelectorToEventFlow y) :=
    congrArg choiceFreeDiagonalSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (choiceFreeDiagonalSelectorRoundTrip x).symm
      (Eq.trans hread (choiceFreeDiagonalSelectorRoundTrip y)))

instance choiceFreeDiagonalSelectorBHistCarrier :
    BHistCarrier ChoiceFreeDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choiceFreeDiagonalSelectorToEventFlow
  fromEventFlow := choiceFreeDiagonalSelectorFromEventFlow

instance choiceFreeDiagonalSelectorChapterTasteGate :
    ChapterTasteGate ChoiceFreeDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      choiceFreeDiagonalSelectorFromEventFlow
        (choiceFreeDiagonalSelectorToEventFlow x) = some x
    exact choiceFreeDiagonalSelectorRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (choiceFreeDiagonalSelectorToEventFlow_injective heq)

theorem ChoiceFreeDiagonalSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      choiceFreeDiagonalSelectorDecodeBHist
        (choiceFreeDiagonalSelectorEncodeBHist h) = h) ∧
      (∀ x : ChoiceFreeDiagonalSelectorUp,
        choiceFreeDiagonalSelectorFromEventFlow
          (choiceFreeDiagonalSelectorToEventFlow x) = some x) ∧
        (∀ x y : ChoiceFreeDiagonalSelectorUp,
          choiceFreeDiagonalSelectorToEventFlow x =
            choiceFreeDiagonalSelectorToEventFlow y → x = y) ∧
          (∀ (x : ChoiceFreeDiagonalSelectorUp) w m,
            List.Mem w (choiceFreeDiagonalSelectorToEventFlow x) →
              List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) ∧
            choiceFreeDiagonalSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact choiceFreeDiagonalSelectorDecodeEncodeBHist
  · constructor
    · intro x
      exact choiceFreeDiagonalSelectorRoundTrip x
    · constructor
      · intro x y heq
        exact choiceFreeDiagonalSelectorToEventFlow_injective heq
      · constructor
        · intro x w m hw hm
          exact BMark_generated_cases m
        · rfl

def taste_gate : (fun _ : BHist => ChapterTasteGate ChoiceFreeDiagonalSelectorUp) BHist.Empty :=
  choiceFreeDiagonalSelectorChapterTasteGate

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp
