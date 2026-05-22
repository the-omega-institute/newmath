import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyEquivalenceUp : Type where
  | mk : (X Y W D Z R E H C P N : BHist) → RegularCauchyEquivalenceUp
  deriving DecidableEq

def regularCauchyEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyEquivalenceEncodeBHist h

def regularCauchyEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyEquivalenceDecodeBHist tail)

private theorem regularCauchyEquivalenceDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyEquivalenceDecodeBHist
        (regularCauchyEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyEquivalenceToEventFlow : RegularCauchyEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N =>
      [[BMark.b0],
        regularCauchyEquivalenceEncodeBHist X,
        [BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyEquivalenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyEquivalenceEncodeBHist N]

def regularCauchyEquivalenceFromEventFlow :
    EventFlow → Option RegularCauchyEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: rest0 =>
      match rest0 with
      | X :: rest1 =>
          match rest1 with
          | _tag1 :: rest2 =>
              match rest2 with
              | Y :: rest3 =>
                  match rest3 with
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | W :: rest5 =>
                          match rest5 with
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | D :: rest7 =>
                                  match rest7 with
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | Z :: rest9 =>
                                          match rest9 with
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RegularCauchyEquivalenceUp.mk
                                                                                                  (regularCauchyEquivalenceDecodeBHist X)
                                                                                                  (regularCauchyEquivalenceDecodeBHist Y)
                                                                                                  (regularCauchyEquivalenceDecodeBHist W)
                                                                                                  (regularCauchyEquivalenceDecodeBHist D)
                                                                                                  (regularCauchyEquivalenceDecodeBHist Z)
                                                                                                  (regularCauchyEquivalenceDecodeBHist R)
                                                                                                  (regularCauchyEquivalenceDecodeBHist E)
                                                                                                  (regularCauchyEquivalenceDecodeBHist H)
                                                                                                  (regularCauchyEquivalenceDecodeBHist C)
                                                                                                  (regularCauchyEquivalenceDecodeBHist P)
                                                                                                  (regularCauchyEquivalenceDecodeBHist N))
                                                                                          | _ :: _ => none
                                                                                      | [] => none
                                                                                  | [] => none
                                                                              | [] => none
                                                                          | [] => none
                                                                      | [] => none
                                                                  | [] => none
                                                              | [] => none
                                                          | [] => none
                                                      | [] => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

def regularCauchyEquivalenceFields :
    RegularCauchyEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N =>
      [X, Y, W, D, Z, R, E, H, C, P, N]

def RegularCauchyEquivalenceCarrier : RegularCauchyEquivalenceUp → Prop
  -- BEDC touchpoint anchor: BHist hsame Cont
  | RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N =>
      hsame X X ∧ hsame Y Y ∧ hsame W W ∧ hsame D D ∧ hsame Z Z ∧
        hsame R R ∧ hsame E E ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
          hsame N N ∧ Cont C BHist.Empty C

private theorem regularCauchyEquivalence_round_trip :
    ∀ x : RegularCauchyEquivalenceUp,
      regularCauchyEquivalenceFromEventFlow
        (regularCauchyEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D Z R E H C P N =>
      change
        some
          (RegularCauchyEquivalenceUp.mk
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist X))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist Y))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist W))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist D))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist Z))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist R))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist E))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist H))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist C))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist P))
            (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist N))) =
          some (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N)
      rw [regularCauchyEquivalenceDecode_encode_bhist X,
        regularCauchyEquivalenceDecode_encode_bhist Y,
        regularCauchyEquivalenceDecode_encode_bhist W,
        regularCauchyEquivalenceDecode_encode_bhist D,
        regularCauchyEquivalenceDecode_encode_bhist Z,
        regularCauchyEquivalenceDecode_encode_bhist R,
        regularCauchyEquivalenceDecode_encode_bhist E,
        regularCauchyEquivalenceDecode_encode_bhist H,
        regularCauchyEquivalenceDecode_encode_bhist C,
        regularCauchyEquivalenceDecode_encode_bhist P,
        regularCauchyEquivalenceDecode_encode_bhist N]

private theorem regularCauchyEquivalenceToEventFlow_injective
    {x y : RegularCauchyEquivalenceUp} :
    regularCauchyEquivalenceToEventFlow x =
      regularCauchyEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyEquivalenceFromEventFlow
          (regularCauchyEquivalenceToEventFlow x) =
        regularCauchyEquivalenceFromEventFlow
          (regularCauchyEquivalenceToEventFlow y) :=
    congrArg regularCauchyEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyEquivalence_round_trip x).symm
      (Eq.trans hread (regularCauchyEquivalence_round_trip y)))

private theorem regularCauchyEquivalenceFields_faithful :
    ∀ x y : RegularCauchyEquivalenceUp,
      regularCauchyEquivalenceFields x = regularCauchyEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X1 Y1 W1 D1 Z1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 W2 D2 Z2 R2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance regularCauchyEquivalenceBHistCarrier :
    BHistCarrier RegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyEquivalenceToEventFlow
  fromEventFlow := regularCauchyEquivalenceFromEventFlow

instance regularCauchyEquivalenceChapterTasteGate :
    ChapterTasteGate RegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyEquivalenceFromEventFlow
        (regularCauchyEquivalenceToEventFlow x) = some x
    exact regularCauchyEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyEquivalenceToEventFlow_injective heq)

instance regularCauchyEquivalenceFieldFaithful :
    FieldFaithful RegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyEquivalenceFields
  field_faithful := regularCauchyEquivalenceFields_faithful

instance regularCauchyEquivalenceNontrivial :
    Nontrivial RegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RegularCauchyEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyEquivalenceDecodeBHist
        (regularCauchyEquivalenceEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyEquivalenceUp,
        regularCauchyEquivalenceFromEventFlow
          (regularCauchyEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyEquivalenceUp,
          regularCauchyEquivalenceToEventFlow x =
            regularCauchyEquivalenceToEventFlow y → x = y) ∧
          regularCauchyEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RegularCauchyEquivalenceUp,
              regularCauchyEquivalenceFields x =
                regularCauchyEquivalenceFields y → x = y) ∧
              (∃ x y : RegularCauchyEquivalenceUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyEquivalenceDecode_encode_bhist
  · constructor
    · exact regularCauchyEquivalence_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyEquivalenceToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact regularCauchyEquivalenceFields_faithful
          · exact
              ⟨RegularCauchyEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                RegularCauchyEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

theorem RegularCauchyEquivalenceCarrier_refinement_transport
    {X Y W D Z R E H C P N Xp Yp Wp Dp Zp Rp Ep Hp Cp Pp Np : BHist}
    (hX : hsame X Xp) (hY : hsame Y Yp) (hW : hsame W Wp) (hD : hsame D Dp)
    (hZ : hsame Z Zp) (hR : hsame R Rp) (hE : hsame E Ep) (hH : hsame H Hp)
    (hC : hsame C Cp) (hP : hsame P Pp) (hN : hsame N Np) :
    RegularCauchyEquivalenceCarrier
        (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N) ->
      RegularCauchyEquivalenceCarrier
          (RegularCauchyEquivalenceUp.mk Xp Yp Wp Dp Zp Rp Ep Hp Cp Pp Np) ∧
        Cont Cp BHist.Empty Cp := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier
  cases hX
  cases hY
  cases hW
  cases hD
  cases hZ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  exact ⟨carrier, cont_right_unit C⟩

theorem RegularCauchyEquivalence_real_classifier_boundary {X Y W D Z R E H C P N : BHist} :
    RegularCauchyEquivalenceCarrier
        (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N) ->
      hsame R R ∧ hsame E E ∧ Cont C BHist.Empty C ∧
        regularCauchyEquivalenceFields
            (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N) =
          [X, Y, W, D, Z, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier
  rcases carrier with
    ⟨_hX, _hY, _hW, _hD, _hZ, hR, hE, _hH, _hC, _hP, _hN, hCont⟩
  exact ⟨hR, hE, hCont, rfl⟩

namespace TasteGate

theorem RegularCauchyEquivalence_refinement_transport {X Y W D Z R E H C P N : BHist} :
    regularCauchyEquivalenceFields
        (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N) =
        [X, Y, W, D, Z, R, E, H, C, P, N] ∧
      (Cont X W C →
        Cont (regularCauchyEquivalenceDecodeBHist
            (regularCauchyEquivalenceEncodeBHist X))
          (regularCauchyEquivalenceDecodeBHist
            (regularCauchyEquivalenceEncodeBHist W)) C) ∧
        hsame (regularCauchyEquivalenceDecodeBHist
            (regularCauchyEquivalenceEncodeBHist X)) X ∧
          hsame (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist Y)) Y ∧
            hsame (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist W)) W := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · rfl
  · constructor
    · intro route
      have hX := regularCauchyEquivalenceDecode_encode_bhist X
      have hW := regularCauchyEquivalenceDecode_encode_bhist W
      rw [hX, hW]
      exact route
    · constructor
      · exact regularCauchyEquivalenceDecode_encode_bhist X
      · constructor
        · exact regularCauchyEquivalenceDecode_encode_bhist Y
        · exact regularCauchyEquivalenceDecode_encode_bhist W

theorem RegularCauchyEquivalence_real_classifier_boundary
    {X Y W D Z R E H C P N reflected : BHist} :
    regularCauchyEquivalenceFields
        (RegularCauchyEquivalenceUp.mk X Y W D Z R E H C P N) =
        [X, Y, W, D, Z, R, E, H, C, P, N] ∧
      Cont Z R reflected →
        hsame (regularCauchyEquivalenceDecodeBHist
          (regularCauchyEquivalenceEncodeBHist R)) R ∧
          Cont Z R reflected ∧
            hsame (regularCauchyEquivalenceDecodeBHist
              (regularCauchyEquivalenceEncodeBHist E)) E := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro surface
  exact
    ⟨regularCauchyEquivalenceDecode_encode_bhist R,
      surface.right,
      regularCauchyEquivalenceDecode_encode_bhist E⟩

end TasteGate

end BEDC.Derived.RegularCauchyEquivalenceUp
