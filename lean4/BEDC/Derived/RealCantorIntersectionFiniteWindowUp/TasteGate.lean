import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCantorIntersectionFiniteWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCantorIntersectionFiniteWindowUp : Type where
  | mk (I D W R E H C P N : BHist) : RealCantorIntersectionFiniteWindowUp
  deriving DecidableEq

def realCantorIntersectionFiniteWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCantorIntersectionFiniteWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCantorIntersectionFiniteWindowEncodeBHist h

def realCantorIntersectionFiniteWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCantorIntersectionFiniteWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCantorIntersectionFiniteWindowDecodeBHist tail)

private theorem realCantorIntersectionFiniteWindowDecode_encode_bhist :
    ∀ h : BHist,
      realCantorIntersectionFiniteWindowDecodeBHist
        (realCantorIntersectionFiniteWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCantorIntersectionFiniteWindowToEventFlow :
    RealCantorIntersectionFiniteWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCantorIntersectionFiniteWindowUp.mk I D W R E H C P N =>
      [[BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist I,
        [BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCantorIntersectionFiniteWindowEncodeBHist N]

def realCantorIntersectionFiniteWindowFromEventFlow :
    EventFlow → Option RealCantorIntersectionFiniteWindowUp
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
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
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
                                      | E :: rest9 =>
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
                                                                                (RealCantorIntersectionFiniteWindowUp.mk
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist I)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist D)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist W)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist R)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist E)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist H)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist C)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist P)
                                                                                  (realCantorIntersectionFiniteWindowDecodeBHist N))
                                                                          | _ :: _ => none

private theorem realCantorIntersectionFiniteWindow_round_trip :
    ∀ x : RealCantorIntersectionFiniteWindowUp,
      realCantorIntersectionFiniteWindowFromEventFlow
        (realCantorIntersectionFiniteWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D W R E H C P N =>
      change
        some
          (RealCantorIntersectionFiniteWindowUp.mk
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist I))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist D))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist W))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist R))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist E))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist H))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist C))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist P))
            (realCantorIntersectionFiniteWindowDecodeBHist
              (realCantorIntersectionFiniteWindowEncodeBHist N))) =
          some (RealCantorIntersectionFiniteWindowUp.mk I D W R E H C P N)
      rw [realCantorIntersectionFiniteWindowDecode_encode_bhist I,
        realCantorIntersectionFiniteWindowDecode_encode_bhist D,
        realCantorIntersectionFiniteWindowDecode_encode_bhist W,
        realCantorIntersectionFiniteWindowDecode_encode_bhist R,
        realCantorIntersectionFiniteWindowDecode_encode_bhist E,
        realCantorIntersectionFiniteWindowDecode_encode_bhist H,
        realCantorIntersectionFiniteWindowDecode_encode_bhist C,
        realCantorIntersectionFiniteWindowDecode_encode_bhist P,
        realCantorIntersectionFiniteWindowDecode_encode_bhist N]

private theorem realCantorIntersectionFiniteWindowToEventFlow_injective
    {x y : RealCantorIntersectionFiniteWindowUp} :
    realCantorIntersectionFiniteWindowToEventFlow x =
      realCantorIntersectionFiniteWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCantorIntersectionFiniteWindowFromEventFlow
          (realCantorIntersectionFiniteWindowToEventFlow x) =
        realCantorIntersectionFiniteWindowFromEventFlow
          (realCantorIntersectionFiniteWindowToEventFlow y) :=
    congrArg realCantorIntersectionFiniteWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCantorIntersectionFiniteWindow_round_trip x).symm
      (Eq.trans hread (realCantorIntersectionFiniteWindow_round_trip y)))

instance realCantorIntersectionFiniteWindowBHistCarrier :
    BHistCarrier RealCantorIntersectionFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCantorIntersectionFiniteWindowToEventFlow
  fromEventFlow := realCantorIntersectionFiniteWindowFromEventFlow

instance realCantorIntersectionFiniteWindowChapterTasteGate :
    ChapterTasteGate RealCantorIntersectionFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCantorIntersectionFiniteWindowFromEventFlow
        (realCantorIntersectionFiniteWindowToEventFlow x) = some x
    exact realCantorIntersectionFiniteWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCantorIntersectionFiniteWindowToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCantorIntersectionFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCantorIntersectionFiniteWindowChapterTasteGate

instance realCantorIntersectionFiniteWindowFieldFaithful :
    FieldFaithful RealCantorIntersectionFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RealCantorIntersectionFiniteWindowUp.mk I D W R E H C P N =>
        [I, D, W, R, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk I₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk I₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hI t1
            injection t1 with hD t2
            injection t2 with hW t3
            injection t3 with hR t4
            injection t4 with hE t5
            injection t5 with hH t6
            injection t6 with hC t7
            injection t7 with hP t8
            injection t8 with hN _
            cases hI
            cases hD
            cases hW
            cases hR
            cases hE
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance realCantorIntersectionFiniteWindowNontrivial :
    Nontrivial RealCantorIntersectionFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCantorIntersectionFiniteWindowUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCantorIntersectionFiniteWindowUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealCantorIntersectionFiniteWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realCantorIntersectionFiniteWindowDecodeBHist
          (realCantorIntersectionFiniteWindowEncodeBHist h) = h) ∧
      (∀ x : RealCantorIntersectionFiniteWindowUp,
        realCantorIntersectionFiniteWindowFromEventFlow
          (realCantorIntersectionFiniteWindowToEventFlow x) = some x) ∧
        (∀ x y : RealCantorIntersectionFiniteWindowUp,
          realCantorIntersectionFiniteWindowToEventFlow x =
            realCantorIntersectionFiniteWindowToEventFlow y ->
              x = y) ∧
          realCantorIntersectionFiniteWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realCantorIntersectionFiniteWindowDecode_encode_bhist
  · constructor
    · exact realCantorIntersectionFiniteWindow_round_trip
    · constructor
      · intro x y heq
        exact realCantorIntersectionFiniteWindowToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealCantorIntersectionFiniteWindowUp
