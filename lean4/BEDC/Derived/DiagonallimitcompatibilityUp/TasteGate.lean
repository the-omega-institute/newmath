import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalLimitCompatibilityUp : Type where
  | mk (R T S D W Q L H C P N : BHist) : DiagonalLimitCompatibilityUp
  deriving DecidableEq

def diagonalLimitCompatibilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalLimitCompatibilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalLimitCompatibilityEncodeBHist h

def diagonalLimitCompatibilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalLimitCompatibilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalLimitCompatibilityDecodeBHist tail)

private theorem diagonalLimitCompatibilityDecode_encode_bhist :
    ∀ h : BHist,
      diagonalLimitCompatibilityDecodeBHist (diagonalLimitCompatibilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem diagonalLimitCompatibility_mk_congr
    {R R' T T' S S' D D' W W' Q Q' L L' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hT : T' = T) (hS : S' = S) (hD : D' = D) (hW : W' = W)
    (hQ : Q' = Q) (hL : L' = L) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    DiagonalLimitCompatibilityUp.mk R' T' S' D' W' Q' L' H' C' P' N' =
      DiagonalLimitCompatibilityUp.mk R T S D W Q L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hT
  cases hS
  cases hD
  cases hW
  cases hQ
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def diagonalLimitCompatibilityToEventFlow : DiagonalLimitCompatibilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitCompatibilityUp.mk R T S D W Q L H C P N =>
      [[BMark.b0],
        diagonalLimitCompatibilityEncodeBHist R,
        [BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalLimitCompatibilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitCompatibilityEncodeBHist N]

def diagonalLimitCompatibilityFromEventFlow : EventFlow → Option DiagonalLimitCompatibilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | W :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | Q :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | L :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (DiagonalLimitCompatibilityUp.mk
                                                                                                  (diagonalLimitCompatibilityDecodeBHist R)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist T)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist S)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist D)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist W)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist Q)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist L)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist H)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist C)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist P)
                                                                                                  (diagonalLimitCompatibilityDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem diagonalLimitCompatibility_round_trip :
    ∀ x : DiagonalLimitCompatibilityUp,
      diagonalLimitCompatibilityFromEventFlow (diagonalLimitCompatibilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R T S D W Q L H C P N =>
      change
        some
          (DiagonalLimitCompatibilityUp.mk
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist R))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist T))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist S))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist D))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist W))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist Q))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist L))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist H))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist C))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist P))
            (diagonalLimitCompatibilityDecodeBHist
              (diagonalLimitCompatibilityEncodeBHist N))) =
          some (DiagonalLimitCompatibilityUp.mk R T S D W Q L H C P N)
      exact
        congrArg some
          (diagonalLimitCompatibility_mk_congr
            (diagonalLimitCompatibilityDecode_encode_bhist R)
            (diagonalLimitCompatibilityDecode_encode_bhist T)
            (diagonalLimitCompatibilityDecode_encode_bhist S)
            (diagonalLimitCompatibilityDecode_encode_bhist D)
            (diagonalLimitCompatibilityDecode_encode_bhist W)
            (diagonalLimitCompatibilityDecode_encode_bhist Q)
            (diagonalLimitCompatibilityDecode_encode_bhist L)
            (diagonalLimitCompatibilityDecode_encode_bhist H)
            (diagonalLimitCompatibilityDecode_encode_bhist C)
            (diagonalLimitCompatibilityDecode_encode_bhist P)
            (diagonalLimitCompatibilityDecode_encode_bhist N))

private theorem diagonalLimitCompatibilityToEventFlow_injective
    {x y : DiagonalLimitCompatibilityUp} :
    diagonalLimitCompatibilityToEventFlow x = diagonalLimitCompatibilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalLimitCompatibilityFromEventFlow (diagonalLimitCompatibilityToEventFlow x) =
        diagonalLimitCompatibilityFromEventFlow (diagonalLimitCompatibilityToEventFlow y) :=
    congrArg diagonalLimitCompatibilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalLimitCompatibility_round_trip x).symm
      (Eq.trans hread (diagonalLimitCompatibility_round_trip y)))

def diagonalLimitCompatibilityFields : DiagonalLimitCompatibilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitCompatibilityUp.mk R T S D W Q L H C P N => [R, T, S, D, W, Q, L, H, C, P, N]

private theorem diagonalLimitCompatibility_field_faithful :
    ∀ x y : DiagonalLimitCompatibilityUp,
      diagonalLimitCompatibilityFields x = diagonalLimitCompatibilityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk R₁ T₁ S₁ D₁ W₁ Q₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ T₂ S₂ D₂ W₂ Q₂ L₂ H₂ C₂ P₂ N₂ =>
          injection h with hR t1
          injection t1 with hT t2
          injection t2 with hS t3
          injection t3 with hD t4
          injection t4 with hW t5
          injection t5 with hQ t6
          injection t6 with hL t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          cases hR
          cases hT
          cases hS
          cases hD
          cases hW
          cases hQ
          cases hL
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance diagonalLimitCompatibilityBHistCarrier : BHistCarrier DiagonalLimitCompatibilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalLimitCompatibilityToEventFlow
  fromEventFlow := diagonalLimitCompatibilityFromEventFlow

instance diagonalLimitCompatibilityChapterTasteGate :
    ChapterTasteGate DiagonalLimitCompatibilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diagonalLimitCompatibilityFromEventFlow (diagonalLimitCompatibilityToEventFlow x) =
        some x
    exact diagonalLimitCompatibility_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalLimitCompatibilityToEventFlow_injective heq)

instance diagonalLimitCompatibilityFieldFaithful :
    FieldFaithful DiagonalLimitCompatibilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diagonalLimitCompatibilityFields
  field_faithful := diagonalLimitCompatibility_field_faithful

instance diagonalLimitCompatibilityNontrivial : Nontrivial DiagonalLimitCompatibilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalLimitCompatibilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalLimitCompatibilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiagonalLimitCompatibilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalLimitCompatibilityChapterTasteGate

def taste_gate_witness : FieldFaithful DiagonalLimitCompatibilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalLimitCompatibilityFieldFaithful

theorem DiagonalLimitCompatibilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      diagonalLimitCompatibilityDecodeBHist (diagonalLimitCompatibilityEncodeBHist h) = h) ∧
      (∀ x : DiagonalLimitCompatibilityUp,
        diagonalLimitCompatibilityFromEventFlow (diagonalLimitCompatibilityToEventFlow x) =
          some x) ∧
        (∀ x y : DiagonalLimitCompatibilityUp,
          diagonalLimitCompatibilityToEventFlow x =
            diagonalLimitCompatibilityToEventFlow y → x = y) ∧
          diagonalLimitCompatibilityEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : DiagonalLimitCompatibilityUp,
              diagonalLimitCompatibilityFields x = diagonalLimitCompatibilityFields y →
                x = y) ∧
              (∃ x y : DiagonalLimitCompatibilityUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact diagonalLimitCompatibilityDecode_encode_bhist
  · constructor
    · exact diagonalLimitCompatibility_round_trip
    · constructor
      · intro x y heq
        exact diagonalLimitCompatibilityToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact diagonalLimitCompatibility_field_faithful
          · exact
              ⟨DiagonalLimitCompatibilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                DiagonalLimitCompatibilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
