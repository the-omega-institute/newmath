import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalModelAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalModelAuditUp : Type where
  | mk : (Q R O M C T Y D L F S H U P N : BHist) → PhysicalModelAuditUp

def physicalModelAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalModelAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalModelAuditEncodeBHist h

def physicalModelAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalModelAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalModelAuditDecodeBHist tail)

private theorem physicalModelAuditDecode_encode_bhist :
    ∀ h : BHist, physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def physicalModelAuditToEventFlow : PhysicalModelAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalModelAuditUp.mk Q R O M C T Y D L F S H U P N =>
      [physicalModelAuditEncodeBHist Q,
        physicalModelAuditEncodeBHist R,
        physicalModelAuditEncodeBHist O,
        physicalModelAuditEncodeBHist M,
        physicalModelAuditEncodeBHist C,
        physicalModelAuditEncodeBHist T,
        physicalModelAuditEncodeBHist Y,
        physicalModelAuditEncodeBHist D,
        physicalModelAuditEncodeBHist L,
        physicalModelAuditEncodeBHist F,
        physicalModelAuditEncodeBHist S,
        physicalModelAuditEncodeBHist H,
        physicalModelAuditEncodeBHist U,
        physicalModelAuditEncodeBHist P,
        physicalModelAuditEncodeBHist N]

def physicalModelAuditFromEventFlow : EventFlow → Option PhysicalModelAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Y :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | L :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | F :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | S :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | U :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | N :: rest14 =>
                                                              match rest14 with
                                                              | [] =>
                                                                  some
                                                                    (PhysicalModelAuditUp.mk
                                                                      (physicalModelAuditDecodeBHist Q)
                                                                      (physicalModelAuditDecodeBHist R)
                                                                      (physicalModelAuditDecodeBHist O)
                                                                      (physicalModelAuditDecodeBHist M)
                                                                      (physicalModelAuditDecodeBHist C)
                                                                      (physicalModelAuditDecodeBHist T)
                                                                      (physicalModelAuditDecodeBHist Y)
                                                                      (physicalModelAuditDecodeBHist D)
                                                                      (physicalModelAuditDecodeBHist L)
                                                                      (physicalModelAuditDecodeBHist F)
                                                                      (physicalModelAuditDecodeBHist S)
                                                                      (physicalModelAuditDecodeBHist H)
                                                                      (physicalModelAuditDecodeBHist U)
                                                                      (physicalModelAuditDecodeBHist P)
                                                                      (physicalModelAuditDecodeBHist N))
                                                              | _ :: _ => none

private theorem physicalModelAudit_round_trip :
    ∀ x : PhysicalModelAuditUp,
      physicalModelAuditFromEventFlow (physicalModelAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q R O M C T Y D L F S H U P N =>
      change
        some
          (PhysicalModelAuditUp.mk
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist Q))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist R))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist O))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist M))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist C))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist T))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist Y))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist D))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist L))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist F))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist S))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist H))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist U))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist P))
            (physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist N))) =
        some (PhysicalModelAuditUp.mk Q R O M C T Y D L F S H U P N)
      rw [physicalModelAuditDecode_encode_bhist Q, physicalModelAuditDecode_encode_bhist R,
        physicalModelAuditDecode_encode_bhist O, physicalModelAuditDecode_encode_bhist M,
        physicalModelAuditDecode_encode_bhist C, physicalModelAuditDecode_encode_bhist T,
        physicalModelAuditDecode_encode_bhist Y, physicalModelAuditDecode_encode_bhist D,
        physicalModelAuditDecode_encode_bhist L, physicalModelAuditDecode_encode_bhist F,
        physicalModelAuditDecode_encode_bhist S, physicalModelAuditDecode_encode_bhist H,
        physicalModelAuditDecode_encode_bhist U, physicalModelAuditDecode_encode_bhist P,
        physicalModelAuditDecode_encode_bhist N]

theorem physicalModelAuditToEventFlow_injective {x y : PhysicalModelAuditUp} :
    physicalModelAuditToEventFlow x = physicalModelAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk Q1 R1 O1 M1 C1 T1 Y1 D1 L1 F1 S1 H1 U1 P1 N1 =>
      cases y with
      | mk Q2 R2 O2 M2 C2 T2 Y2 D2 L2 F2 S2 H2 U2 P2 N2 =>
          injection heq with hQ tail1
          injection tail1 with hR tail2
          injection tail2 with hO tail3
          injection tail3 with hM tail4
          injection tail4 with hC tail5
          injection tail5 with hT tail6
          injection tail6 with hY tail7
          injection tail7 with hD tail8
          injection tail8 with hL tail9
          injection tail9 with hF tail10
          injection tail10 with hS tail11
          injection tail11 with hH tail12
          injection tail12 with hU tail13
          injection tail13 with hP tail14
          injection tail14 with hN _
          have hQ' : Q1 = Q2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hQ
            exact Eq.trans (physicalModelAuditDecode_encode_bhist Q1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist Q2))
          cases hQ'
          have hR' : R1 = R2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hR
            exact Eq.trans (physicalModelAuditDecode_encode_bhist R1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist R2))
          cases hR'
          have hO' : O1 = O2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hO
            exact Eq.trans (physicalModelAuditDecode_encode_bhist O1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist O2))
          cases hO'
          have hM' : M1 = M2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hM
            exact Eq.trans (physicalModelAuditDecode_encode_bhist M1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist M2))
          cases hM'
          have hC' : C1 = C2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hC
            exact Eq.trans (physicalModelAuditDecode_encode_bhist C1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist C2))
          cases hC'
          have hT' : T1 = T2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hT
            exact Eq.trans (physicalModelAuditDecode_encode_bhist T1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist T2))
          cases hT'
          have hY' : Y1 = Y2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hY
            exact Eq.trans (physicalModelAuditDecode_encode_bhist Y1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist Y2))
          cases hY'
          have hD' : D1 = D2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hD
            exact Eq.trans (physicalModelAuditDecode_encode_bhist D1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist D2))
          cases hD'
          have hL' : L1 = L2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hL
            exact Eq.trans (physicalModelAuditDecode_encode_bhist L1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist L2))
          cases hL'
          have hF' : F1 = F2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hF
            exact Eq.trans (physicalModelAuditDecode_encode_bhist F1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist F2))
          cases hF'
          have hS' : S1 = S2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hS
            exact Eq.trans (physicalModelAuditDecode_encode_bhist S1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist S2))
          cases hS'
          have hH' : H1 = H2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hH
            exact Eq.trans (physicalModelAuditDecode_encode_bhist H1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist H2))
          cases hH'
          have hU' : U1 = U2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hU
            exact Eq.trans (physicalModelAuditDecode_encode_bhist U1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist U2))
          cases hU'
          have hP' : P1 = P2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hP
            exact Eq.trans (physicalModelAuditDecode_encode_bhist P1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist P2))
          cases hP'
          have hN' : N1 = N2 := by
            have decoded := congrArg physicalModelAuditDecodeBHist hN
            exact Eq.trans (physicalModelAuditDecode_encode_bhist N1).symm
              (Eq.trans decoded (physicalModelAuditDecode_encode_bhist N2))
          cases hN'
          rfl

def physicalModelAuditExplicitBHistCarrier : BHistCarrier PhysicalModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalModelAuditToEventFlow
  fromEventFlow := physicalModelAuditFromEventFlow

def physicalModelAuditExplicitChapterTasteGate :
    @ChapterTasteGate PhysicalModelAuditUp physicalModelAuditExplicitBHistCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  letI : BHistCarrier PhysicalModelAuditUp := physicalModelAuditExplicitBHistCarrier
  {
    round_trip := by
      intro x
      change physicalModelAuditFromEventFlow (physicalModelAuditToEventFlow x) = some x
      exact physicalModelAudit_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (physicalModelAuditToEventFlow_injective heq)
  }

def physicalModelAuditExplicitFieldFaithful :
    @FieldFaithful PhysicalModelAuditUp physicalModelAuditExplicitBHistCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  letI : BHistCarrier PhysicalModelAuditUp := physicalModelAuditExplicitBHistCarrier
  {
    fields := fun x =>
      match x with
      | PhysicalModelAuditUp.mk Q R O M C T Y D L F S H U P N =>
          [Q, R, O, M, C, T, Y, D, L, F, S, H, U, P, N]
    field_faithful := by
      -- BEDC touchpoint anchor: BHist BMark
      intro x y h
      cases x with
      | mk Q1 R1 O1 M1 C1 T1 Y1 D1 L1 F1 S1 H1 U1 P1 N1 =>
          cases y with
          | mk Q2 R2 O2 M2 C2 T2 Y2 D2 L2 F2 S2 H2 U2 P2 N2 =>
              change
                [Q1, R1, O1, M1, C1, T1, Y1, D1, L1, F1, S1, H1, U1, P1, N1] =
                  [Q2, R2, O2, M2, C2, T2, Y2, D2, L2, F2, S2, H2, U2, P2, N2] at h
              cases h
              rfl
  }

instance physicalModelAuditBHistCarrier : BHistCarrier PhysicalModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalModelAuditToEventFlow
  fromEventFlow := physicalModelAuditFromEventFlow

instance physicalModelAuditChapterTasteGate : ChapterTasteGate PhysicalModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicalModelAuditFromEventFlow (physicalModelAuditToEventFlow x) = some x
    exact physicalModelAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalModelAuditToEventFlow_injective heq)

instance physicalModelAuditFieldFaithful : FieldFaithful PhysicalModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PhysicalModelAuditUp.mk Q R O M C T Y D L F S H U P N =>
        [Q, R, O, M, C, T, Y, D, L, F, S, H, U, P, N]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk Q1 R1 O1 M1 C1 T1 Y1 D1 L1 F1 S1 H1 U1 P1 N1 =>
        cases y with
        | mk Q2 R2 O2 M2 C2 T2 Y2 D2 L2 F2 S2 H2 U2 P2 N2 =>
            change
              [Q1, R1, O1, M1, C1, T1, Y1, D1, L1, F1, S1, H1, U1, P1, N1] =
                [Q2, R2, O2, M2, C2, T2, Y2, D2, L2, F2, S2, H2, U2, P2, N2] at h
            cases h
            rfl

instance physicalModelAuditNontrivial : Nontrivial PhysicalModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalModelAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      PhysicalModelAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PhysicalModelAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicalModelAuditDecodeBHist (physicalModelAuditEncodeBHist h) = h) ∧
      (∀ x : PhysicalModelAuditUp,
        physicalModelAuditFromEventFlow (physicalModelAuditToEventFlow x) = some x) ∧
        (∀ x y : PhysicalModelAuditUp,
          physicalModelAuditToEventFlow x = physicalModelAuditToEventFlow y → x = y) ∧
          Nonempty
            (@ChapterTasteGate PhysicalModelAuditUp physicalModelAuditExplicitBHistCarrier) ∧
            Nonempty
              (@FieldFaithful PhysicalModelAuditUp physicalModelAuditExplicitBHistCarrier) ∧
              physicalModelAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact physicalModelAuditDecode_encode_bhist
  · constructor
    · exact physicalModelAudit_round_trip
    · constructor
      · intro x y heq
        exact physicalModelAuditToEventFlow_injective heq
      · constructor
        · exact Nonempty.intro physicalModelAuditExplicitChapterTasteGate
        · constructor
          · exact Nonempty.intro physicalModelAuditExplicitFieldFaithful
          · rfl

end BEDC.Derived.PhysicalModelAuditUp
