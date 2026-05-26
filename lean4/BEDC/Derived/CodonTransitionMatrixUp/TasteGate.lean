import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CodonTransitionMatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CodonTransitionMatrixUp : Type where
  | mk (W Q F D T H C P N : BHist) : CodonTransitionMatrixUp
  deriving DecidableEq

def codonTransitionMatrixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: codonTransitionMatrixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: codonTransitionMatrixEncodeBHist h

def codonTransitionMatrixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (codonTransitionMatrixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (codonTransitionMatrixDecodeBHist tail)

private theorem codonTransitionMatrix_decode_encode_bhist :
    ∀ h : BHist,
      codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def codonTransitionMatrixFields : CodonTransitionMatrixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CodonTransitionMatrixUp.mk W Q F D T H C P N => [W, Q, F, D, T, H, C, P, N]

def codonTransitionMatrixToEventFlow : CodonTransitionMatrixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (codonTransitionMatrixFields x).map codonTransitionMatrixEncodeBHist

def codonTransitionMatrixFromEventFlow : EventFlow → Option CodonTransitionMatrixUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | W :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CodonTransitionMatrixUp.mk
                                              (codonTransitionMatrixDecodeBHist W)
                                              (codonTransitionMatrixDecodeBHist Q)
                                              (codonTransitionMatrixDecodeBHist F)
                                              (codonTransitionMatrixDecodeBHist D)
                                              (codonTransitionMatrixDecodeBHist T)
                                              (codonTransitionMatrixDecodeBHist H)
                                              (codonTransitionMatrixDecodeBHist C)
                                              (codonTransitionMatrixDecodeBHist P)
                                              (codonTransitionMatrixDecodeBHist N))
                                      | _ :: _ => none

private theorem codonTransitionMatrix_round_trip :
    ∀ x : CodonTransitionMatrixUp,
      codonTransitionMatrixFromEventFlow (codonTransitionMatrixToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W Q F D T H C P N =>
      change
        some
          (CodonTransitionMatrixUp.mk
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist W))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist Q))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist F))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) =
          some (CodonTransitionMatrixUp.mk W Q F D T H C P N)
      have hW := codonTransitionMatrix_decode_encode_bhist W
      have hQ := codonTransitionMatrix_decode_encode_bhist Q
      have hF := codonTransitionMatrix_decode_encode_bhist F
      have hD := codonTransitionMatrix_decode_encode_bhist D
      have hT := codonTransitionMatrix_decode_encode_bhist T
      have hH := codonTransitionMatrix_decode_encode_bhist H
      have hC := codonTransitionMatrix_decode_encode_bhist C
      have hP := codonTransitionMatrix_decode_encode_bhist P
      have hN := codonTransitionMatrix_decode_encode_bhist N
      apply congrArg some
      exact
        Eq.trans
          (congrArg
            (fun z =>
              CodonTransitionMatrixUp.mk z
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist Q))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist F))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hW)
          (Eq.trans
            (congrArg
              (fun z =>
                CodonTransitionMatrixUp.mk W z
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist F))
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                  (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hQ)
            (Eq.trans
              (congrArg
                (fun z =>
                  CodonTransitionMatrixUp.mk W Q z
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hF)
              (Eq.trans
                (congrArg
                  (fun z =>
                    CodonTransitionMatrixUp.mk W Q F z
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hD)
                (Eq.trans
                  (congrArg
                    (fun z =>
                      CodonTransitionMatrixUp.mk W Q F D z
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                        (codonTransitionMatrixDecodeBHist
                          (codonTransitionMatrixEncodeBHist N))) hT)
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        CodonTransitionMatrixUp.mk W Q F D T z
                          (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                          (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                          (codonTransitionMatrixDecodeBHist
                            (codonTransitionMatrixEncodeBHist N))) hH)
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          CodonTransitionMatrixUp.mk W Q F D T H z
                            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                            (codonTransitionMatrixDecodeBHist
                              (codonTransitionMatrixEncodeBHist N))) hC)
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            CodonTransitionMatrixUp.mk W Q F D T H C z
                              (codonTransitionMatrixDecodeBHist
                                (codonTransitionMatrixEncodeBHist N))) hP)
                        (congrArg (fun z => CodonTransitionMatrixUp.mk W Q F D T H C P z)
                          hN))))))))

private theorem codonTransitionMatrixToEventFlow_injective {x y : CodonTransitionMatrixUp} :
    codonTransitionMatrixToEventFlow x = codonTransitionMatrixToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      codonTransitionMatrixFromEventFlow (codonTransitionMatrixToEventFlow x) =
        codonTransitionMatrixFromEventFlow (codonTransitionMatrixToEventFlow y) :=
    congrArg codonTransitionMatrixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (codonTransitionMatrix_round_trip x).symm
      (Eq.trans hread (codonTransitionMatrix_round_trip y)))

private theorem codonTransitionMatrix_field_faithful :
    ∀ x y : CodonTransitionMatrixUp,
      codonTransitionMatrixFields x = codonTransitionMatrixFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 Q1 F1 D1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 Q2 F2 D2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance codonTransitionMatrixBHistCarrier : BHistCarrier CodonTransitionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := codonTransitionMatrixToEventFlow
  fromEventFlow := codonTransitionMatrixFromEventFlow

instance codonTransitionMatrixChapterTasteGate :
    ChapterTasteGate CodonTransitionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change codonTransitionMatrixFromEventFlow (codonTransitionMatrixToEventFlow x) = some x
    exact codonTransitionMatrix_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (codonTransitionMatrixToEventFlow_injective heq)

instance codonTransitionMatrixFieldFaithful : FieldFaithful CodonTransitionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := codonTransitionMatrixFields
  field_faithful := codonTransitionMatrix_field_faithful

instance codonTransitionMatrixNontrivial : Nontrivial CodonTransitionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CodonTransitionMatrixUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CodonTransitionMatrixUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CodonTransitionMatrixTasteGate_single_carrier_alignment :
    (∀ h : BHist, codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist h) = h) ∧
      (∀ x : CodonTransitionMatrixUp,
        codonTransitionMatrixFromEventFlow (codonTransitionMatrixToEventFlow x) = some x) ∧
        (∀ x y : CodonTransitionMatrixUp,
          codonTransitionMatrixToEventFlow x = codonTransitionMatrixToEventFlow y → x = y) ∧
          codonTransitionMatrixFields
              (CodonTransitionMatrixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk W Q F D T H C P N =>
          change
            some
              (CodonTransitionMatrixUp.mk
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist W))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist Q))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist F))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) =
              some (CodonTransitionMatrixUp.mk W Q F D T H C P N)
          have hW := codonTransitionMatrix_decode_encode_bhist W
          have hQ := codonTransitionMatrix_decode_encode_bhist Q
          have hF := codonTransitionMatrix_decode_encode_bhist F
          have hD := codonTransitionMatrix_decode_encode_bhist D
          have hT := codonTransitionMatrix_decode_encode_bhist T
          have hH := codonTransitionMatrix_decode_encode_bhist H
          have hC := codonTransitionMatrix_decode_encode_bhist C
          have hP := codonTransitionMatrix_decode_encode_bhist P
          have hN := codonTransitionMatrix_decode_encode_bhist N
          apply congrArg some
          exact
            Eq.trans
              (congrArg
                (fun z =>
                  CodonTransitionMatrixUp.mk z
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist Q))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist F))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                    (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hW)
              (Eq.trans
                (congrArg
                  (fun z =>
                    CodonTransitionMatrixUp.mk W z
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist F))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                      (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hQ)
                (Eq.trans
                  (congrArg
                    (fun z =>
                      CodonTransitionMatrixUp.mk W Q z
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist D))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                        (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist N))) hF)
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        CodonTransitionMatrixUp.mk W Q F z
                          (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist T))
                          (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                          (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                          (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                          (codonTransitionMatrixDecodeBHist
                            (codonTransitionMatrixEncodeBHist N))) hD)
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          CodonTransitionMatrixUp.mk W Q F D z
                            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist H))
                            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist C))
                            (codonTransitionMatrixDecodeBHist (codonTransitionMatrixEncodeBHist P))
                            (codonTransitionMatrixDecodeBHist
                              (codonTransitionMatrixEncodeBHist N))) hT)
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            CodonTransitionMatrixUp.mk W Q F D T z
                              (codonTransitionMatrixDecodeBHist
                                (codonTransitionMatrixEncodeBHist C))
                              (codonTransitionMatrixDecodeBHist
                                (codonTransitionMatrixEncodeBHist P))
                              (codonTransitionMatrixDecodeBHist
                                (codonTransitionMatrixEncodeBHist N))) hH)
                        (Eq.trans
                          (congrArg
                            (fun z =>
                              CodonTransitionMatrixUp.mk W Q F D T H z
                                (codonTransitionMatrixDecodeBHist
                                  (codonTransitionMatrixEncodeBHist P))
                                (codonTransitionMatrixDecodeBHist
                                  (codonTransitionMatrixEncodeBHist N))) hC)
                          (Eq.trans
                            (congrArg
                              (fun z =>
                                CodonTransitionMatrixUp.mk W Q F D T H C z
                                  (codonTransitionMatrixDecodeBHist
                                    (codonTransitionMatrixEncodeBHist N))) hP)
                            (congrArg
                              (fun z => CodonTransitionMatrixUp.mk W Q F D T H C P z)
                              hN))))))))
    · constructor
      · intro x y heq
        cases x with
        | mk W1 Q1 F1 D1 T1 H1 C1 P1 N1 =>
            cases y with
            | mk W2 Q2 F2 D2 T2 H2 C2 P2 N2 =>
                injection heq with hW htail0
                injection htail0 with hQ htail1
                injection htail1 with hF htail2
                injection htail2 with hD htail3
                injection htail3 with hT htail4
                injection htail4 with hH htail5
                injection htail5 with hC htail6
                injection htail6 with hP htail7
                injection htail7 with hN _
                have hW' : W1 = W2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hW
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist W1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist W2))
                cases hW'
                have hQ' : Q1 = Q2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hQ
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist Q1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist Q2))
                cases hQ'
                have hF' : F1 = F2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hF
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist F1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist F2))
                cases hF'
                have hD' : D1 = D2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hD
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist D1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist D2))
                cases hD'
                have hT' : T1 = T2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hT
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist T1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist T2))
                cases hT'
                have hH' : H1 = H2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hH
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist H1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist H2))
                cases hH'
                have hC' : C1 = C2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hC
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist C1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist C2))
                cases hC'
                have hP' : P1 = P2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hP
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist P1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist P2))
                cases hP'
                have hN' : N1 = N2 := by
                  have decoded := congrArg codonTransitionMatrixDecodeBHist hN
                  exact Eq.trans (codonTransitionMatrix_decode_encode_bhist N1).symm
                    (Eq.trans decoded (codonTransitionMatrix_decode_encode_bhist N2))
                cases hN'
                rfl
      · rfl

end BEDC.Derived.CodonTransitionMatrixUp
