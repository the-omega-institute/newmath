import BEDC.Derived.BanachFixedPointIterationBudgetUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachFixedPointIterationBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def banachFixedPointIterationBudgetFields :
    BanachFixedPointIterationBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachFixedPointIterationBudgetUp.mk X T x0 I Q R K H C P N =>
      [X, T, x0, I, Q, R, K, H, C, P, N]

def banachFixedPointIterationBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachFixedPointIterationBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachFixedPointIterationBudgetEncodeBHist h

def banachFixedPointIterationBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachFixedPointIterationBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachFixedPointIterationBudgetDecodeBHist tail)

private theorem BanachFixedPointIterationBudgetTasteGate_decode_encode :
    ∀ h : BHist,
      banachFixedPointIterationBudgetDecodeBHist
        (banachFixedPointIterationBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachFixedPointIterationBudgetToEventFlow :
    BanachFixedPointIterationBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map banachFixedPointIterationBudgetEncodeBHist
      (banachFixedPointIterationBudgetFields x)

def banachFixedPointIterationBudgetFromEventFlow :
    EventFlow → Option BanachFixedPointIterationBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | x0 :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | K :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (BanachFixedPointIterationBudgetUp.mk
                                                      (banachFixedPointIterationBudgetDecodeBHist X)
                                                      (banachFixedPointIterationBudgetDecodeBHist T)
                                                      (banachFixedPointIterationBudgetDecodeBHist x0)
                                                      (banachFixedPointIterationBudgetDecodeBHist I)
                                                      (banachFixedPointIterationBudgetDecodeBHist Q)
                                                      (banachFixedPointIterationBudgetDecodeBHist R)
                                                      (banachFixedPointIterationBudgetDecodeBHist K)
                                                      (banachFixedPointIterationBudgetDecodeBHist H)
                                                      (banachFixedPointIterationBudgetDecodeBHist C)
                                                      (banachFixedPointIterationBudgetDecodeBHist P)
                                                      (banachFixedPointIterationBudgetDecodeBHist N))
                                              | _ :: _ => none

private theorem BanachFixedPointIterationBudgetTasteGate_round_trip :
    ∀ x : BanachFixedPointIterationBudgetUp,
      banachFixedPointIterationBudgetFromEventFlow
        (banachFixedPointIterationBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T x0 I Q R K H C P N =>
      change
        some
          (BanachFixedPointIterationBudgetUp.mk
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist X))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist T))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist x0))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist I))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist Q))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist R))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist K))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist H))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist C))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist P))
            (banachFixedPointIterationBudgetDecodeBHist
              (banachFixedPointIterationBudgetEncodeBHist N))) =
          some (BanachFixedPointIterationBudgetUp.mk X T x0 I Q R K H C P N)
      rw [BanachFixedPointIterationBudgetTasteGate_decode_encode X,
        BanachFixedPointIterationBudgetTasteGate_decode_encode T,
        BanachFixedPointIterationBudgetTasteGate_decode_encode x0,
        BanachFixedPointIterationBudgetTasteGate_decode_encode I,
        BanachFixedPointIterationBudgetTasteGate_decode_encode Q,
        BanachFixedPointIterationBudgetTasteGate_decode_encode R,
        BanachFixedPointIterationBudgetTasteGate_decode_encode K,
        BanachFixedPointIterationBudgetTasteGate_decode_encode H,
        BanachFixedPointIterationBudgetTasteGate_decode_encode C,
        BanachFixedPointIterationBudgetTasteGate_decode_encode P,
        BanachFixedPointIterationBudgetTasteGate_decode_encode N]

private theorem BanachFixedPointIterationBudgetTasteGate_toEventFlow_injective
    {x y : BanachFixedPointIterationBudgetUp} :
    banachFixedPointIterationBudgetToEventFlow x =
      banachFixedPointIterationBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachFixedPointIterationBudgetFromEventFlow
          (banachFixedPointIterationBudgetToEventFlow x) =
        banachFixedPointIterationBudgetFromEventFlow
          (banachFixedPointIterationBudgetToEventFlow y) :=
    congrArg banachFixedPointIterationBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BanachFixedPointIterationBudgetTasteGate_round_trip x).symm
      (Eq.trans hread
        (BanachFixedPointIterationBudgetTasteGate_round_trip y)))

private theorem BanachFixedPointIterationBudgetTasteGate_fields :
    ∀ x y : BanachFixedPointIterationBudgetUp,
      banachFixedPointIterationBudgetFields x =
        banachFixedPointIterationBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 T1 x01 I1 Q1 R1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 T2 x02 I2 Q2 R2 K2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance banachFixedPointIterationBudgetBHistCarrier :
    BHistCarrier BanachFixedPointIterationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachFixedPointIterationBudgetToEventFlow
  fromEventFlow := banachFixedPointIterationBudgetFromEventFlow

instance banachFixedPointIterationBudgetChapterTasteGate :
    ChapterTasteGate BanachFixedPointIterationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      banachFixedPointIterationBudgetFromEventFlow
        (banachFixedPointIterationBudgetToEventFlow x) = some x
    exact BanachFixedPointIterationBudgetTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachFixedPointIterationBudgetTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BanachFixedPointIterationBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachFixedPointIterationBudgetChapterTasteGate

instance banachFixedPointIterationBudgetFieldFaithful :
    FieldFaithful BanachFixedPointIterationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachFixedPointIterationBudgetFields
  field_faithful := BanachFixedPointIterationBudgetTasteGate_fields

theorem BanachFixedPointIterationBudgetCarrier_contracting_step_budget
    {X T x0 I Q R K H C P N picardTail endpointRead : BHist}
    (x : BanachFixedPointIterationBudgetUp)
    (hx : x = BanachFixedPointIterationBudgetUp.mk X T x0 I Q R K H C P N)
    (picardStep : Cont I Q picardTail)
    (endpointRoute : Cont picardTail K endpointRead) :
    hsame endpointRead (append (append I Q) K) ∧
      List.Mem (banachFixedPointIterationBudgetEncodeBHist Q)
        (BHistCarrier.toEventFlow x) ∧
      hsame C C ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame BHistCarrier
  cases hx
  cases picardStep
  cases endpointRoute
  exact
    ⟨rfl,
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))),
      hsame_refl C, hsame_refl P, hsame_refl N⟩

end BEDC.Derived.BanachFixedPointIterationBudgetUp
