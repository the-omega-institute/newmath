import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# BHistCellRowEmbeddingUp TasteGate carrier.
-/

namespace BEDC.Derived.BHistCellRowEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite cell-row embedding packet with the nine displayed BEDC rows. -/
inductive BHistCellRowEmbeddingUp : Type where
  | mk : (B I W O R H C P N : BHist) → BHistCellRowEmbeddingUp
  deriving DecidableEq

def bhistCellRowEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bhistCellRowEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bhistCellRowEmbeddingEncodeBHist h

def bhistCellRowEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bhistCellRowEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bhistCellRowEmbeddingDecodeBHist tail)

private theorem bhistCellRowEmbeddingDecodeEncodeBHist :
    ∀ h : BHist,
      bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bhistCellRowEmbeddingFields : BHistCellRowEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistCellRowEmbeddingUp.mk B I W O R H C P N => [B, I, W, O, R, H, C, P, N]

def bhistCellRowEmbeddingToEventFlow : BHistCellRowEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistCellRowEmbeddingUp.mk B I W O R H C P N =>
      [[BMark.b0],
        bhistCellRowEmbeddingEncodeBHist B,
        [BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bhistCellRowEmbeddingEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bhistCellRowEmbeddingEncodeBHist N]

def bhistCellRowEmbeddingFromEventFlow : EventFlow → Option BHistCellRowEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
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
                              | O :: rest7 =>
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
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (BHistCellRowEmbeddingUp.mk
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    B)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    I)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    W)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    O)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    R)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    H)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    C)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    P)
                                                                                  (bhistCellRowEmbeddingDecodeBHist
                                                                                    N))
                                                                          | _ :: _ =>
                                                                              none

private theorem bhistCellRowEmbeddingRoundTrip :
    ∀ x : BHistCellRowEmbeddingUp,
      bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B I W O R H C P N =>
      change
        some
          (BHistCellRowEmbeddingUp.mk
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist B))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist I))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist W))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist O))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist R))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist H))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist C))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist P))
            (bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist N))) =
          some (BHistCellRowEmbeddingUp.mk B I W O R H C P N)
      rw [bhistCellRowEmbeddingDecodeEncodeBHist B,
        bhistCellRowEmbeddingDecodeEncodeBHist I,
        bhistCellRowEmbeddingDecodeEncodeBHist W,
        bhistCellRowEmbeddingDecodeEncodeBHist O,
        bhistCellRowEmbeddingDecodeEncodeBHist R,
        bhistCellRowEmbeddingDecodeEncodeBHist H,
        bhistCellRowEmbeddingDecodeEncodeBHist C,
        bhistCellRowEmbeddingDecodeEncodeBHist P,
        bhistCellRowEmbeddingDecodeEncodeBHist N]

private theorem bhistCellRowEmbeddingToEventFlow_injective {x y : BHistCellRowEmbeddingUp} :
    bhistCellRowEmbeddingToEventFlow x = bhistCellRowEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) =
        bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow y) :=
    congrArg bhistCellRowEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bhistCellRowEmbeddingRoundTrip x).symm
      (Eq.trans hread (bhistCellRowEmbeddingRoundTrip y)))

instance bhistCellRowEmbeddingBHistCarrier : BHistCarrier BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bhistCellRowEmbeddingToEventFlow
  fromEventFlow := bhistCellRowEmbeddingFromEventFlow

instance bhistCellRowEmbeddingChapterTasteGate : ChapterTasteGate BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) = some x
    exact bhistCellRowEmbeddingRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bhistCellRowEmbeddingToEventFlow_injective heq)

instance bhistCellRowEmbeddingFieldFaithful : FieldFaithful BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bhistCellRowEmbeddingFields
  field_faithful := by
    intro x y h
    cases x with
    | mk B1 I1 W1 O1 R1 H1 C1 P1 N1 =>
        cases y with
        | mk B2 I2 W2 O2 R2 H2 C2 P2 N2 =>
            injection h with hB tail1
            injection tail1 with hI tail2
            injection tail2 with hW tail3
            injection tail3 with hO tail4
            injection tail4 with hR tail5
            injection tail5 with hH tail6
            injection tail6 with hC tail7
            injection tail7 with hP tail8
            injection tail8 with hN _
            subst hB
            subst hI
            subst hW
            subst hO
            subst hR
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance bhistCellRowEmbeddingNontrivial : BEDC.Meta.TasteGate.Nontrivial
    BHistCellRowEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistCellRowEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistCellRowEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BHistCellRowEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bhistCellRowEmbeddingDecodeBHist (bhistCellRowEmbeddingEncodeBHist h) = h) ∧
      (∀ x : BHistCellRowEmbeddingUp,
        bhistCellRowEmbeddingFromEventFlow (bhistCellRowEmbeddingToEventFlow x) =
          some x) ∧
        (∀ x y : BHistCellRowEmbeddingUp,
          bhistCellRowEmbeddingToEventFlow x = bhistCellRowEmbeddingToEventFlow y →
            x = y) ∧
          bhistCellRowEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact bhistCellRowEmbeddingDecodeEncodeBHist
  · constructor
    · exact bhistCellRowEmbeddingRoundTrip
    · constructor
      · intro x y heq
        exact bhistCellRowEmbeddingToEventFlow_injective heq
      · rfl

end BEDC.Derived.BHistCellRowEmbeddingUp
