import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont.Cancellation
import BEDC.Meta.TasteGate

/-!
# FiniteObservationInterfaceUp TasteGate carrier.
-/

namespace BEDC.Derived.FiniteObservationInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite observation packet with the nine rows displayed by the paper carrier. -/
inductive FiniteObservationInterfaceUp : Type where
  | mk : (S R D T E H C P N : BHist) → FiniteObservationInterfaceUp

def finiteObservationInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationInterfaceEncodeBHist h

def finiteObservationInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationInterfaceDecodeBHist tail)

private theorem finiteObservationInterfaceDecode_encode_bhist :
    ∀ h : BHist,
      finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteObservationInterfaceToEventFlow : FiniteObservationInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationInterfaceUp.mk S R D T E H C P N =>
      [[BMark.b0],
        finiteObservationInterfaceEncodeBHist S,
        [BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteObservationInterfaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteObservationInterfaceEncodeBHist N]

def finiteObservationInterfaceFromEventFlow : EventFlow → Option FiniteObservationInterfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: S :: _tag1 :: R :: _tag2 :: D :: _tag3 :: T :: _tag4 :: E :: _tag5 ::
      H :: _tag6 :: C :: _tag7 :: P :: _tag8 :: N :: [] =>
      some (FiniteObservationInterfaceUp.mk
        (finiteObservationInterfaceDecodeBHist S) (finiteObservationInterfaceDecodeBHist R)
        (finiteObservationInterfaceDecodeBHist D) (finiteObservationInterfaceDecodeBHist T)
        (finiteObservationInterfaceDecodeBHist E) (finiteObservationInterfaceDecodeBHist H)
        (finiteObservationInterfaceDecodeBHist C) (finiteObservationInterfaceDecodeBHist P)
        (finiteObservationInterfaceDecodeBHist N))
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: [] =>
      none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ =>
      none

private theorem finiteObservationInterface_round_trip :
    ∀ x : FiniteObservationInterfaceUp,
      finiteObservationInterfaceFromEventFlow (finiteObservationInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D T E H C P N =>
      change
        some
          (FiniteObservationInterfaceUp.mk
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist S))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist R))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist D))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist T))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist E))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist H))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist C))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist P))
            (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist N))) =
          some (FiniteObservationInterfaceUp.mk S R D T E H C P N)
      have hS := finiteObservationInterfaceDecode_encode_bhist S
      have hR := finiteObservationInterfaceDecode_encode_bhist R
      have hD := finiteObservationInterfaceDecode_encode_bhist D
      have hT := finiteObservationInterfaceDecode_encode_bhist T
      have hE := finiteObservationInterfaceDecode_encode_bhist E
      have hH := finiteObservationInterfaceDecode_encode_bhist H
      have hC := finiteObservationInterfaceDecode_encode_bhist C
      have hP := finiteObservationInterfaceDecode_encode_bhist P
      have hN := finiteObservationInterfaceDecode_encode_bhist N
      apply congrArg some
      exact
        Eq.trans
          (congrArg
            (fun z =>
              FiniteObservationInterfaceUp.mk z
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist R))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist D))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist T))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist E))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist H))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist C))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist P))
                (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist N))) hS)
          (Eq.trans
            (congrArg
              (fun z =>
                FiniteObservationInterfaceUp.mk S z
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist D))
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist T))
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist E))
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist H))
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist C))
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist P))
                  (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist N))) hR)
            (Eq.trans
              (congrArg
                (fun z =>
                  FiniteObservationInterfaceUp.mk S R z
                    (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist T))
                    (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist E))
                    (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist H))
                    (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist C))
                    (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist P))
                    (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist N))) hD)
              (Eq.trans
                (congrArg
                  (fun z =>
                    FiniteObservationInterfaceUp.mk S R D z
                      (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist E))
                      (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist H))
                      (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist C))
                      (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist P))
                      (finiteObservationInterfaceDecodeBHist
                        (finiteObservationInterfaceEncodeBHist N))) hT)
                (Eq.trans
                  (congrArg
                    (fun z =>
                      FiniteObservationInterfaceUp.mk S R D T z
                        (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist H))
                        (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist C))
                        (finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist P))
                        (finiteObservationInterfaceDecodeBHist
                          (finiteObservationInterfaceEncodeBHist N))) hE)
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        FiniteObservationInterfaceUp.mk S R D T E z
                          (finiteObservationInterfaceDecodeBHist
                            (finiteObservationInterfaceEncodeBHist C))
                          (finiteObservationInterfaceDecodeBHist
                            (finiteObservationInterfaceEncodeBHist P))
                          (finiteObservationInterfaceDecodeBHist
                            (finiteObservationInterfaceEncodeBHist N))) hH)
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          FiniteObservationInterfaceUp.mk S R D T E H z
                            (finiteObservationInterfaceDecodeBHist
                              (finiteObservationInterfaceEncodeBHist P))
                            (finiteObservationInterfaceDecodeBHist
                              (finiteObservationInterfaceEncodeBHist N))) hC)
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            FiniteObservationInterfaceUp.mk S R D T E H C z
                              (finiteObservationInterfaceDecodeBHist
                                (finiteObservationInterfaceEncodeBHist N))) hP)
                        (congrArg (fun z => FiniteObservationInterfaceUp.mk S R D T E H C P z)
                          hN))))))))

theorem finiteObservationInterfaceToEventFlow_injective {x y : FiniteObservationInterfaceUp} :
    finiteObservationInterfaceToEventFlow x = finiteObservationInterfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S1 R1 D1 T1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 T2 E2 H2 C2 P2 N2 =>
          injection heq with _ htail0
          injection htail0 with hS htail1
          injection htail1 with _ htail2
          injection htail2 with hR htail3
          injection htail3 with _ htail4
          injection htail4 with hD htail5
          injection htail5 with _ htail6
          injection htail6 with hT htail7
          injection htail7 with _ htail8
          injection htail8 with hE htail9
          injection htail9 with _ htail10
          injection htail10 with hH htail11
          injection htail11 with _ htail12
          injection htail12 with hC htail13
          injection htail13 with _ htail14
          injection htail14 with hP htail15
          injection htail15 with _ htail16
          injection htail16 with hN _
          have hS' : S1 = S2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hS
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist S1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist S2))
          cases hS'
          have hR' : R1 = R2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hR
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist R1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist R2))
          cases hR'
          have hD' : D1 = D2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hD
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist D1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist D2))
          cases hD'
          have hT' : T1 = T2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hT
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist T1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist T2))
          cases hT'
          have hE' : E1 = E2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hE
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist E1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist E2))
          cases hE'
          have hH' : H1 = H2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hH
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist H1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist H2))
          cases hH'
          have hC' : C1 = C2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hC
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist C1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist C2))
          cases hC'
          have hP' : P1 = P2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hP
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist P1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist P2))
          cases hP'
          have hN' : N1 = N2 := by
            have decoded := congrArg finiteObservationInterfaceDecodeBHist hN
            exact Eq.trans (finiteObservationInterfaceDecode_encode_bhist N1).symm
              (Eq.trans decoded (finiteObservationInterfaceDecode_encode_bhist N2))
          cases hN'
          rfl

instance finiteObservationInterfaceBHistCarrier : BHistCarrier FiniteObservationInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationInterfaceToEventFlow
  fromEventFlow := finiteObservationInterfaceFromEventFlow

instance finiteObservationInterfaceChapterTasteGate :
    ChapterTasteGate FiniteObservationInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationInterfaceFromEventFlow (finiteObservationInterfaceToEventFlow x) = some x
    exact finiteObservationInterface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteObservationInterfaceToEventFlow_injective heq)

instance finiteObservationInterfaceFieldFaithful :
    FieldFaithful FiniteObservationInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteObservationInterfaceUp.mk S R D T E H C P N => [S, R, D, T, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk S1 R1 D1 T1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk S2 R2 D2 T2 E2 H2 C2 P2 N2 =>
            cases h
            rfl

def taste_gate : ChapterTasteGate FiniteObservationInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationInterfaceChapterTasteGate

theorem FiniteObservationInterfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteObservationInterfaceDecodeBHist (finiteObservationInterfaceEncodeBHist h) = h) ∧
      (∀ x : FiniteObservationInterfaceUp,
        finiteObservationInterfaceFromEventFlow (finiteObservationInterfaceToEventFlow x) =
          some x) ∧
      (∀ x y : FiniteObservationInterfaceUp,
        finiteObservationInterfaceToEventFlow x = finiteObservationInterfaceToEventFlow y →
          x = y) ∧
      finiteObservationInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteObservationInterfaceDecode_encode_bhist
  · constructor
    · exact finiteObservationInterface_round_trip
    · constructor
      · intro x y heq
        exact finiteObservationInterfaceToEventFlow_injective heq
      · rfl

theorem FiniteObservationInterfaceSelectedStream_handoff
    {S R D T E H C P N T' H' E' C' : BHist}
    (selectedRoute : Cont BHist.Empty T H)
    (tailLedgerRoute : Cont T E C)
    (hT : hsame T T')
    (hH : hsame H H')
    (hE : hsame E E')
    (hC : hsame C C') :
    Cont BHist.Empty T' H' ∧
      Cont T' E' C' ∧
        finiteObservationInterfaceFromEventFlow
          (finiteObservationInterfaceToEventFlow
            (FiniteObservationInterfaceUp.mk S R D T E H C P N)) =
          some (FiniteObservationInterfaceUp.mk S R D T E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · exact cont_hsame_transport (show hsame BHist.Empty BHist.Empty from rfl) hT hH
      selectedRoute
  · constructor
    · exact cont_hsame_transport hT hE hC tailLedgerRoute
    · exact finiteObservationInterface_round_trip
        (FiniteObservationInterfaceUp.mk S R D T E H C P N)

theorem FiniteObservationInterfaceNameCert_obligation_surface
    {S R D T E H C P N S' R' D' T' E' H' C' P' N' : BHist}
    (hS : hsame S S')
    (hR : hsame R R')
    (hD : hsame D D')
    (hT : hsame T T')
    (hE : hsame E E')
    (hH : hsame H H')
    (hC : hsame C C')
    (hP : hsame P P')
    (hN : hsame N N')
    (streamRegular : Cont S R C)
    (regularDyadic : Cont R D C)
    (selectedTail : Cont T E H) :
    Cont S' R' C' ∧
      Cont R' D' C' ∧
        Cont T' E' H' ∧
          finiteObservationInterfaceFromEventFlow
            (finiteObservationInterfaceToEventFlow
              (FiniteObservationInterfaceUp.mk S R D T E H C P N)) =
            some (FiniteObservationInterfaceUp.mk S R D T E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases hP
  cases hN
  constructor
  · exact cont_hsame_transport hS hR hC streamRegular
  · constructor
    · exact cont_hsame_transport hR hD hC regularDyadic
    · constructor
      · exact cont_hsame_transport hT hE hH selectedTail
      · exact finiteObservationInterface_round_trip
          (FiniteObservationInterfaceUp.mk S R D T E H C P N)

end BEDC.Derived.FiniteObservationInterfaceUp
