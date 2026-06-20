import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanOrderedCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanOrderedCauchyCompletionUp : Type where
  | mk : (D S Q R O L H C P N : BHist) → ArchimedeanOrderedCauchyCompletionUp
  deriving DecidableEq

def archimedeanOrderedCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanOrderedCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanOrderedCauchyCompletionEncodeBHist h

def archimedeanOrderedCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanOrderedCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanOrderedCauchyCompletionDecodeBHist tail)

private theorem archimedeanOrderedCauchyCompletion_decode_encode :
    ∀ h : BHist,
      archimedeanOrderedCauchyCompletionDecodeBHist
        (archimedeanOrderedCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanOrderedCauchyCompletionFields :
    ArchimedeanOrderedCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanOrderedCauchyCompletionUp.mk D S Q R O L H C P N =>
      [D, S, Q, R, O, L, H, C, P, N]

def archimedeanOrderedCauchyCompletionToEventFlow :
    ArchimedeanOrderedCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (archimedeanOrderedCauchyCompletionFields x).map
        archimedeanOrderedCauchyCompletionEncodeBHist

def archimedeanOrderedCauchyCompletionFromEventFlow :
    EventFlow → Option ArchimedeanOrderedCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | O :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ArchimedeanOrderedCauchyCompletionUp.mk
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist D)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist S)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist Q)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist R)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist O)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist L)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist H)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist C)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist P)
                                                  (archimedeanOrderedCauchyCompletionDecodeBHist N))
                                          | _ :: _ => none

private theorem archimedeanOrderedCauchyCompletion_round_trip :
    ∀ x : ArchimedeanOrderedCauchyCompletionUp,
      archimedeanOrderedCauchyCompletionFromEventFlow
        (archimedeanOrderedCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S Q R O L H C P N =>
      change
        some
          (ArchimedeanOrderedCauchyCompletionUp.mk
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist D))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist S))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist Q))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist R))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist O))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist L))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist H))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist C))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist P))
            (archimedeanOrderedCauchyCompletionDecodeBHist
              (archimedeanOrderedCauchyCompletionEncodeBHist N))) =
          some (ArchimedeanOrderedCauchyCompletionUp.mk D S Q R O L H C P N)
      rw [archimedeanOrderedCauchyCompletion_decode_encode D,
        archimedeanOrderedCauchyCompletion_decode_encode S,
        archimedeanOrderedCauchyCompletion_decode_encode Q,
        archimedeanOrderedCauchyCompletion_decode_encode R,
        archimedeanOrderedCauchyCompletion_decode_encode O,
        archimedeanOrderedCauchyCompletion_decode_encode L,
        archimedeanOrderedCauchyCompletion_decode_encode H,
        archimedeanOrderedCauchyCompletion_decode_encode C,
        archimedeanOrderedCauchyCompletion_decode_encode P,
        archimedeanOrderedCauchyCompletion_decode_encode N]

private theorem archimedeanOrderedCauchyCompletionToEventFlow_injective
    {x y : ArchimedeanOrderedCauchyCompletionUp} :
    archimedeanOrderedCauchyCompletionToEventFlow x =
      archimedeanOrderedCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanOrderedCauchyCompletionFromEventFlow
          (archimedeanOrderedCauchyCompletionToEventFlow x) =
        archimedeanOrderedCauchyCompletionFromEventFlow
          (archimedeanOrderedCauchyCompletionToEventFlow y) :=
    congrArg archimedeanOrderedCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (archimedeanOrderedCauchyCompletion_round_trip x).symm
      (Eq.trans hread (archimedeanOrderedCauchyCompletion_round_trip y)))

private theorem archimedeanOrderedCauchyCompletion_fields_faithful :
    ∀ x y : ArchimedeanOrderedCauchyCompletionUp,
      archimedeanOrderedCauchyCompletionFields x =
        archimedeanOrderedCauchyCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D1 S1 Q1 R1 O1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 Q2 R2 O2 L2 H2 C2 P2 N2 =>
          injection h with hD t1
          injection t1 with hS t2
          injection t2 with hQ t3
          injection t3 with hR t4
          injection t4 with hO t5
          injection t5 with hL t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hD
          subst hS
          subst hQ
          subst hR
          subst hO
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance archimedeanOrderedCauchyCompletionBHistCarrier :
    BHistCarrier ArchimedeanOrderedCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanOrderedCauchyCompletionToEventFlow
  fromEventFlow := archimedeanOrderedCauchyCompletionFromEventFlow

instance archimedeanOrderedCauchyCompletionChapterTasteGate :
    ChapterTasteGate ArchimedeanOrderedCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanOrderedCauchyCompletionFromEventFlow
          (archimedeanOrderedCauchyCompletionToEventFlow x) =
        some x
    exact archimedeanOrderedCauchyCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanOrderedCauchyCompletionToEventFlow_injective heq)

instance archimedeanOrderedCauchyCompletionFieldFaithful :
    FieldFaithful ArchimedeanOrderedCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanOrderedCauchyCompletionFields
  field_faithful := archimedeanOrderedCauchyCompletion_fields_faithful

instance archimedeanOrderedCauchyCompletionNontrivial :
    Nontrivial ArchimedeanOrderedCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArchimedeanOrderedCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArchimedeanOrderedCauchyCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ArchimedeanOrderedCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanOrderedCauchyCompletionChapterTasteGate

theorem ArchimedeanOrderedCauchyCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      archimedeanOrderedCauchyCompletionDecodeBHist
        (archimedeanOrderedCauchyCompletionEncodeBHist h) = h) ∧
      (∀ x : ArchimedeanOrderedCauchyCompletionUp,
        archimedeanOrderedCauchyCompletionFromEventFlow
          (archimedeanOrderedCauchyCompletionToEventFlow x) = some x) ∧
      (∀ x y : ArchimedeanOrderedCauchyCompletionUp,
        archimedeanOrderedCauchyCompletionToEventFlow x =
          archimedeanOrderedCauchyCompletionToEventFlow y → x = y) ∧
      archimedeanOrderedCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  let decodeEncode :
      ∀ h : BHist,
        archimedeanOrderedCauchyCompletionDecodeBHist
          (archimedeanOrderedCauchyCompletionEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  let roundTrip :
      ∀ x : ArchimedeanOrderedCauchyCompletionUp,
        archimedeanOrderedCauchyCompletionFromEventFlow
          (archimedeanOrderedCauchyCompletionToEventFlow x) = some x := by
    intro x
    cases x with
    | mk D S Q R O L H C P N =>
        change
          some
            (ArchimedeanOrderedCauchyCompletionUp.mk
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist D))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist S))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist Q))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist R))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist O))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist L))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist H))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist C))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist P))
              (archimedeanOrderedCauchyCompletionDecodeBHist
                (archimedeanOrderedCauchyCompletionEncodeBHist N))) =
            some (ArchimedeanOrderedCauchyCompletionUp.mk D S Q R O L H C P N)
        let mkCongr
            {D' S' Q' R' O' L' H' C' P' N' : BHist}
            (hD : D' = D)
            (hS : S' = S)
            (hQ : Q' = Q)
            (hR : R' = R)
            (hO : O' = O)
            (hL : L' = L)
            (hH : H' = H)
            (hC : C' = C)
            (hP : P' = P)
            (hN : N' = N) :
            ArchimedeanOrderedCauchyCompletionUp.mk D' S' Q' R' O' L' H' C' P' N' =
              ArchimedeanOrderedCauchyCompletionUp.mk D S Q R O L H C P N := by
          cases hD
          cases hS
          cases hQ
          cases hR
          cases hO
          cases hL
          cases hH
          cases hC
          cases hP
          cases hN
          rfl
        exact
          congrArg some
            (mkCongr (decodeEncode D) (decodeEncode S) (decodeEncode Q)
              (decodeEncode R) (decodeEncode O) (decodeEncode L) (decodeEncode H)
              (decodeEncode C) (decodeEncode P) (decodeEncode N))
  let toEventFlowInjective :
      ∀ x y : ArchimedeanOrderedCauchyCompletionUp,
        archimedeanOrderedCauchyCompletionToEventFlow x =
          archimedeanOrderedCauchyCompletionToEventFlow y → x = y := by
    intro x y heq
    have hread :
        archimedeanOrderedCauchyCompletionFromEventFlow
            (archimedeanOrderedCauchyCompletionToEventFlow x) =
          archimedeanOrderedCauchyCompletionFromEventFlow
            (archimedeanOrderedCauchyCompletionToEventFlow y) :=
      congrArg archimedeanOrderedCauchyCompletionFromEventFlow heq
    exact Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))
  exact
    ⟨decodeEncode, roundTrip, fun x y heq => toEventFlowInjective x y heq, rfl⟩

end BEDC.Derived.ArchimedeanOrderedCauchyCompletionUp
