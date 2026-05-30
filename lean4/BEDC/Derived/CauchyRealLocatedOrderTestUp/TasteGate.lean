import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealLocatedOrderTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealLocatedOrderTestUp : Type where
  | mk (X Y W D Q O A L H C P N : BHist) : CauchyRealLocatedOrderTestUp
  deriving DecidableEq

def cauchyRealLocatedOrderTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealLocatedOrderTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealLocatedOrderTestEncodeBHist h

def cauchyRealLocatedOrderTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealLocatedOrderTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealLocatedOrderTestDecodeBHist tail)

private theorem CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRealLocatedOrderTestDecodeBHist
        (cauchyRealLocatedOrderTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRealLocatedOrderTestFields :
    CauchyRealLocatedOrderTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealLocatedOrderTestUp.mk X Y W D Q O A L H C P N =>
      [X, Y, W, D, Q, O, A, L, H, C, P, N]

def cauchyRealLocatedOrderTestToEventFlow :
    CauchyRealLocatedOrderTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealLocatedOrderTestFields x).map cauchyRealLocatedOrderTestEncodeBHist

def cauchyRealLocatedOrderTestFromEventFlow :
    EventFlow → Option CauchyRealLocatedOrderTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | leftSource :: rest0 =>
      match rest0 with
      | [] => none
      | rightSource :: rest1 =>
          match rest1 with
          | [] => none
          | windows :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | comparison :: rest4 =>
                      match rest4 with
                      | [] => none
                      | orderRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | apartness :: rest6 =>
                              match rest6 with
                              | [] => none
                              | located :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nameRow :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (CauchyRealLocatedOrderTestUp.mk
                                                          (cauchyRealLocatedOrderTestDecodeBHist leftSource)
                                                          (cauchyRealLocatedOrderTestDecodeBHist rightSource)
                                                          (cauchyRealLocatedOrderTestDecodeBHist windows)
                                                          (cauchyRealLocatedOrderTestDecodeBHist dyadic)
                                                          (cauchyRealLocatedOrderTestDecodeBHist comparison)
                                                          (cauchyRealLocatedOrderTestDecodeBHist orderRow)
                                                          (cauchyRealLocatedOrderTestDecodeBHist apartness)
                                                          (cauchyRealLocatedOrderTestDecodeBHist located)
                                                          (cauchyRealLocatedOrderTestDecodeBHist transport)
                                                          (cauchyRealLocatedOrderTestDecodeBHist replay)
                                                          (cauchyRealLocatedOrderTestDecodeBHist provenance)
                                                          (cauchyRealLocatedOrderTestDecodeBHist nameRow))
                                                  | _ :: _ => none

private theorem CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealLocatedOrderTestUp,
      cauchyRealLocatedOrderTestFromEventFlow
        (cauchyRealLocatedOrderTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D Q O A L H C P N =>
      change
        some
          (CauchyRealLocatedOrderTestUp.mk
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist X))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist Y))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist W))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist D))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist Q))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist O))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist A))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist L))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist H))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist C))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist P))
            (cauchyRealLocatedOrderTestDecodeBHist
              (cauchyRealLocatedOrderTestEncodeBHist N))) =
          some (CauchyRealLocatedOrderTestUp.mk X Y W D Q O A L H C P N)
      rw [CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode X,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode Y,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode W,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode O,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode L,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealLocatedOrderTestUp} :
    cauchyRealLocatedOrderTestToEventFlow x =
      cauchyRealLocatedOrderTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealLocatedOrderTestFromEventFlow
          (cauchyRealLocatedOrderTestToEventFlow x) =
        cauchyRealLocatedOrderTestFromEventFlow
          (cauchyRealLocatedOrderTestToEventFlow y) :=
    congrArg cauchyRealLocatedOrderTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyRealLocatedOrderTestUp,
      cauchyRealLocatedOrderTestFields x =
        cauchyRealLocatedOrderTestFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ W₁ D₁ Q₁ O₁ A₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ W₂ D₂ Q₂ O₂ A₂ L₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX t0
          injection t0 with hY t1
          injection t1 with hW t2
          injection t2 with hD t3
          injection t3 with hQ t4
          injection t4 with hO t5
          injection t5 with hA t6
          injection t6 with hL t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          subst hX
          subst hY
          subst hW
          subst hD
          subst hQ
          subst hO
          subst hA
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyRealLocatedOrderTestBHistCarrier :
    BHistCarrier CauchyRealLocatedOrderTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealLocatedOrderTestToEventFlow
  fromEventFlow := cauchyRealLocatedOrderTestFromEventFlow

instance cauchyRealLocatedOrderTestChapterTasteGate :
    ChapterTasteGate CauchyRealLocatedOrderTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyRealLocatedOrderTestFromEventFlow
        (cauchyRealLocatedOrderTestToEventFlow x) = some x
    exact CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealLocatedOrderTestFieldFaithful :
    FieldFaithful CauchyRealLocatedOrderTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealLocatedOrderTestFields
  field_faithful := CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_fields_faithful

instance cauchyRealLocatedOrderTestNontrivial :
    Nontrivial CauchyRealLocatedOrderTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealLocatedOrderTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyRealLocatedOrderTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRealLocatedOrderTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealLocatedOrderTestChapterTasteGate

theorem CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealLocatedOrderTestDecodeBHist
      (cauchyRealLocatedOrderTestEncodeBHist h) = h) ∧
      (∀ x : CauchyRealLocatedOrderTestUp,
        cauchyRealLocatedOrderTestFromEventFlow
          (cauchyRealLocatedOrderTestToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealLocatedOrderTestUp,
          cauchyRealLocatedOrderTestToEventFlow x =
            cauchyRealLocatedOrderTestToEventFlow y → x = y) ∧
          cauchyRealLocatedOrderTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_decode_encode,
      CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyRealLocatedOrderTestTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyRealLocatedOrderTestUp
