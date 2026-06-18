import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealSubsequenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealSubsequenceModulusUp : Type where
  | mk (K S B W D R E H C P N : BHist) : CompactRealSubsequenceModulusUp

def compactRealSubsequenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealSubsequenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealSubsequenceModulusEncodeBHist h

def compactRealSubsequenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealSubsequenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealSubsequenceModulusDecodeBHist tail)

private theorem compactRealSubsequenceModulusDecodeEncodeBHist :
    ∀ h : BHist,
      compactRealSubsequenceModulusDecodeBHist
        (compactRealSubsequenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRealSubsequenceModulusFields :
    CompactRealSubsequenceModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealSubsequenceModulusUp.mk K S B W D R E H C P N =>
      [K, S, B, W, D, R, E, H, C, P, N]

def compactRealSubsequenceModulusToEventFlow :
    CompactRealSubsequenceModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealSubsequenceModulusUp.mk K S B W D R E H C P N =>
      [compactRealSubsequenceModulusEncodeBHist K,
        compactRealSubsequenceModulusEncodeBHist S,
        compactRealSubsequenceModulusEncodeBHist B,
        compactRealSubsequenceModulusEncodeBHist W,
        compactRealSubsequenceModulusEncodeBHist D,
        compactRealSubsequenceModulusEncodeBHist R,
        compactRealSubsequenceModulusEncodeBHist E,
        compactRealSubsequenceModulusEncodeBHist H,
        compactRealSubsequenceModulusEncodeBHist C,
        compactRealSubsequenceModulusEncodeBHist P,
        compactRealSubsequenceModulusEncodeBHist N]

def compactRealSubsequenceModulusFromEventFlow :
    EventFlow → Option CompactRealSubsequenceModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest =>
      match rest with
      | [] => none
      | S :: rest =>
          match rest with
          | [] => none
          | B :: rest =>
              match rest with
              | [] => none
              | W :: rest =>
                  match rest with
                  | [] => none
                  | D :: rest =>
                      match rest with
                      | [] => none
                      | R :: rest =>
                          match rest with
                          | [] => none
                          | E :: rest =>
                              match rest with
                              | [] => none
                              | H :: rest =>
                                  match rest with
                                  | [] => none
                                  | C :: rest =>
                                      match rest with
                                      | [] => none
                                      | P :: rest =>
                                          match rest with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (CompactRealSubsequenceModulusUp.mk
                                                      (compactRealSubsequenceModulusDecodeBHist K)
                                                      (compactRealSubsequenceModulusDecodeBHist S)
                                                      (compactRealSubsequenceModulusDecodeBHist B)
                                                      (compactRealSubsequenceModulusDecodeBHist W)
                                                      (compactRealSubsequenceModulusDecodeBHist D)
                                                      (compactRealSubsequenceModulusDecodeBHist R)
                                                      (compactRealSubsequenceModulusDecodeBHist E)
                                                      (compactRealSubsequenceModulusDecodeBHist H)
                                                      (compactRealSubsequenceModulusDecodeBHist C)
                                                      (compactRealSubsequenceModulusDecodeBHist P)
                                                      (compactRealSubsequenceModulusDecodeBHist N))
                                              | _ :: _ => none

private theorem compactRealSubsequenceModulusRoundTrip
    (x : CompactRealSubsequenceModulusUp) :
    compactRealSubsequenceModulusFromEventFlow
      (compactRealSubsequenceModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K S B W D R E H C P N =>
      change
        some
          (CompactRealSubsequenceModulusUp.mk
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist K))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist S))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist B))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist W))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist D))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist R))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist E))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist H))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist C))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist P))
            (compactRealSubsequenceModulusDecodeBHist
              (compactRealSubsequenceModulusEncodeBHist N))) =
          some (CompactRealSubsequenceModulusUp.mk K S B W D R E H C P N)
      rw [compactRealSubsequenceModulusDecodeEncodeBHist K,
        compactRealSubsequenceModulusDecodeEncodeBHist S,
        compactRealSubsequenceModulusDecodeEncodeBHist B,
        compactRealSubsequenceModulusDecodeEncodeBHist W,
        compactRealSubsequenceModulusDecodeEncodeBHist D,
        compactRealSubsequenceModulusDecodeEncodeBHist R,
        compactRealSubsequenceModulusDecodeEncodeBHist E,
        compactRealSubsequenceModulusDecodeEncodeBHist H,
        compactRealSubsequenceModulusDecodeEncodeBHist C,
        compactRealSubsequenceModulusDecodeEncodeBHist P,
        compactRealSubsequenceModulusDecodeEncodeBHist N]

private theorem compactRealSubsequenceModulusToEventFlow_injective
    {x y : CompactRealSubsequenceModulusUp} :
    compactRealSubsequenceModulusToEventFlow x =
        compactRealSubsequenceModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRealSubsequenceModulusFromEventFlow
          (compactRealSubsequenceModulusToEventFlow x) =
        compactRealSubsequenceModulusFromEventFlow
          (compactRealSubsequenceModulusToEventFlow y) :=
    congrArg compactRealSubsequenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactRealSubsequenceModulusRoundTrip x).symm
      (Eq.trans hread (compactRealSubsequenceModulusRoundTrip y)))

private theorem compactRealSubsequenceModulusFieldsFaithful :
    ∀ x y : CompactRealSubsequenceModulusUp,
      compactRealSubsequenceModulusFields x =
          compactRealSubsequenceModulusFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ S₁ B₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ S₂ B₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hS tail1
          injection tail1 with hB tail2
          injection tail2 with hW tail3
          injection tail3 with hD tail4
          injection tail4 with hR tail5
          injection tail5 with hE tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hK
          subst hS
          subst hB
          subst hW
          subst hD
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance compactRealSubsequenceModulusBHistCarrier :
    BHistCarrier CompactRealSubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealSubsequenceModulusToEventFlow
  fromEventFlow := compactRealSubsequenceModulusFromEventFlow

instance compactRealSubsequenceModulusChapterTasteGate :
    ChapterTasteGate CompactRealSubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRealSubsequenceModulusFromEventFlow
        (compactRealSubsequenceModulusToEventFlow x) = some x
    exact compactRealSubsequenceModulusRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactRealSubsequenceModulusToEventFlow_injective heq)

instance compactRealSubsequenceModulusFieldFaithful :
    FieldFaithful CompactRealSubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactRealSubsequenceModulusFields
  field_faithful := compactRealSubsequenceModulusFieldsFaithful

instance compactRealSubsequenceModulusNontrivial :
    Nontrivial CompactRealSubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactRealSubsequenceModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompactRealSubsequenceModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactRealSubsequenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactRealSubsequenceModulusDecodeBHist (compactRealSubsequenceModulusEncodeBHist h) =
        h) ∧
      (∀ x : CompactRealSubsequenceModulusUp,
        compactRealSubsequenceModulusFromEventFlow
            (compactRealSubsequenceModulusToEventFlow x) =
          some x) ∧
      (∀ x y : CompactRealSubsequenceModulusUp,
        compactRealSubsequenceModulusToEventFlow x =
            compactRealSubsequenceModulusToEventFlow y →
          x = y) ∧
      compactRealSubsequenceModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk K S B W D R E H C P N =>
          change
            some
              (CompactRealSubsequenceModulusUp.mk
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist K))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist S))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist B))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist W))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist D))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist R))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist E))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist H))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist C))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist P))
                (compactRealSubsequenceModulusDecodeBHist
                  (compactRealSubsequenceModulusEncodeBHist N))) =
              some (CompactRealSubsequenceModulusUp.mk K S B W D R E H C P N)
          rw [compactRealSubsequenceModulusDecodeEncodeBHist K,
            compactRealSubsequenceModulusDecodeEncodeBHist S,
            compactRealSubsequenceModulusDecodeEncodeBHist B,
            compactRealSubsequenceModulusDecodeEncodeBHist W,
            compactRealSubsequenceModulusDecodeEncodeBHist D,
            compactRealSubsequenceModulusDecodeEncodeBHist R,
            compactRealSubsequenceModulusDecodeEncodeBHist E,
            compactRealSubsequenceModulusDecodeEncodeBHist H,
            compactRealSubsequenceModulusDecodeEncodeBHist C,
            compactRealSubsequenceModulusDecodeEncodeBHist P,
            compactRealSubsequenceModulusDecodeEncodeBHist N]
    · constructor
      · intro x y heq
        have hread :
            compactRealSubsequenceModulusFromEventFlow
                (compactRealSubsequenceModulusToEventFlow x) =
              compactRealSubsequenceModulusFromEventFlow
                (compactRealSubsequenceModulusToEventFlow y) :=
          congrArg compactRealSubsequenceModulusFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (compactRealSubsequenceModulusRoundTrip x).symm
            (Eq.trans hread (compactRealSubsequenceModulusRoundTrip y)))
      · rfl

end BEDC.Derived.CompactRealSubsequenceModulusUp
