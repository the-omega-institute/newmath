import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RefuterTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RefuterTraceUp : Type where
  | mk : (A U F E H C P N : BHist) → RefuterTraceUp
  deriving DecidableEq

def refuterTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: refuterTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: refuterTraceEncodeBHist h

def refuterTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (refuterTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (refuterTraceDecodeBHist tail)

private theorem refuterTraceDecode_encode_bhist :
    ∀ h : BHist, refuterTraceDecodeBHist (refuterTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def refuterTraceToEventFlow : RefuterTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RefuterTraceUp.mk A U F E H C P N =>
      [[BMark.b0],
        refuterTraceEncodeBHist A,
        [BMark.b1, BMark.b0],
        refuterTraceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        refuterTraceEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        refuterTraceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        refuterTraceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        refuterTraceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        refuterTraceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        refuterTraceEncodeBHist N]

def refuterTraceFromEventFlow : EventFlow → Option RefuterTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
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
                                                                        (RefuterTraceUp.mk
                                                                          (refuterTraceDecodeBHist A)
                                                                          (refuterTraceDecodeBHist U)
                                                                          (refuterTraceDecodeBHist F)
                                                                          (refuterTraceDecodeBHist E)
                                                                          (refuterTraceDecodeBHist H)
                                                                          (refuterTraceDecodeBHist C)
                                                                          (refuterTraceDecodeBHist P)
                                                                          (refuterTraceDecodeBHist N))
                                                                  | _ :: _ => none

private theorem refuterTrace_round_trip :
    ∀ x : RefuterTraceUp, refuterTraceFromEventFlow (refuterTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A U F E H C P N =>
      change
        some
          (RefuterTraceUp.mk
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist A))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist U))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist F))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist E))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist H))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist C))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist P))
            (refuterTraceDecodeBHist (refuterTraceEncodeBHist N))) =
          some (RefuterTraceUp.mk A U F E H C P N)
      rw [refuterTraceDecode_encode_bhist A, refuterTraceDecode_encode_bhist U,
        refuterTraceDecode_encode_bhist F, refuterTraceDecode_encode_bhist E,
        refuterTraceDecode_encode_bhist H, refuterTraceDecode_encode_bhist C,
        refuterTraceDecode_encode_bhist P, refuterTraceDecode_encode_bhist N]

private theorem refuterTraceToEventFlow_injective {x y : RefuterTraceUp} :
    refuterTraceToEventFlow x = refuterTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      refuterTraceFromEventFlow (refuterTraceToEventFlow x) =
        refuterTraceFromEventFlow (refuterTraceToEventFlow y) :=
    congrArg refuterTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (refuterTrace_round_trip x).symm
      (Eq.trans hread (refuterTrace_round_trip y)))

instance refuterTraceBHistCarrier : BHistCarrier RefuterTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := refuterTraceToEventFlow
  fromEventFlow := refuterTraceFromEventFlow

instance refuterTraceChapterTasteGate : ChapterTasteGate RefuterTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change refuterTraceFromEventFlow (refuterTraceToEventFlow x) = some x
    exact refuterTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (refuterTraceToEventFlow_injective heq)

instance refuterTraceFieldFaithful : FieldFaithful RefuterTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RefuterTraceUp.mk A U F E H C P N => [A, U, F, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk A₁ U₁ F₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ U₂ F₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hA t1
            injection t1 with hU t2
            injection t2 with hF t3
            injection t3 with hE t4
            injection t4 with hH t5
            injection t5 with hC t6
            injection t6 with hP t7
            injection t7 with hN _
            subst hA
            subst hU
            subst hF
            subst hE
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance refuterTraceNontrivial : Nontrivial RefuterTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RefuterTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RefuterTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RefuterTraceTasteGate_single_carrier_alignment :
    (refuterTraceDecodeBHist (refuterTraceEncodeBHist BHist.Empty) = BHist.Empty) ∧
      (refuterTraceDecodeBHist (refuterTraceEncodeBHist (BHist.e1 BHist.Empty)) =
        BHist.e1 BHist.Empty) ∧
        (∀ x : RefuterTraceUp,
          refuterTraceFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (∀ x y : RefuterTraceUp,
            BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) ∧
            ChapterTasteGate RefuterTraceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · intro x
        change refuterTraceFromEventFlow (refuterTraceToEventFlow x) = some x
        exact refuterTrace_round_trip x
      · constructor
        · intro x y heq
          apply refuterTraceToEventFlow_injective
          exact heq
        · exact refuterTraceChapterTasteGate

end BEDC.Derived.RefuterTraceUp
