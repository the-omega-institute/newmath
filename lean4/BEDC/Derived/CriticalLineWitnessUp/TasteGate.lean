import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CriticalLineWitnessUp : Type where
  | mk (Z S M R Q H C P N : BHist) : CriticalLineWitnessUp
  deriving DecidableEq

def criticalLineWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: criticalLineWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: criticalLineWitnessEncodeBHist h

def criticalLineWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (criticalLineWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (criticalLineWitnessDecodeBHist tail)

private theorem criticalLineWitness_decode_encode_bhist :
    ∀ h : BHist, criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def criticalLineWitnessFields : CriticalLineWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CriticalLineWitnessUp.mk Z S M R Q H C P N => [Z, S, M, R, Q, H, C, P, N]

def criticalLineWitnessToEventFlow : CriticalLineWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CriticalLineWitnessUp.mk Z S M R Q H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0],
        criticalLineWitnessEncodeBHist Z,
        criticalLineWitnessEncodeBHist S,
        criticalLineWitnessEncodeBHist M,
        criticalLineWitnessEncodeBHist R,
        criticalLineWitnessEncodeBHist Q,
        criticalLineWitnessEncodeBHist H,
        criticalLineWitnessEncodeBHist C,
        criticalLineWitnessEncodeBHist P,
        criticalLineWitnessEncodeBHist N]

def criticalLineWitnessFromEventFlow :
    EventFlow → Option CriticalLineWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b1, BMark.b1, BMark.b0], Z, S, M, R, Q, H, C, P, N] =>
      some
        (CriticalLineWitnessUp.mk
          (criticalLineWitnessDecodeBHist Z)
          (criticalLineWitnessDecodeBHist S)
          (criticalLineWitnessDecodeBHist M)
          (criticalLineWitnessDecodeBHist R)
          (criticalLineWitnessDecodeBHist Q)
          (criticalLineWitnessDecodeBHist H)
          (criticalLineWitnessDecodeBHist C)
          (criticalLineWitnessDecodeBHist P)
          (criticalLineWitnessDecodeBHist N))
  | _ => none

private theorem criticalLineWitness_round_trip :
    ∀ x : CriticalLineWitnessUp,
      criticalLineWitnessFromEventFlow (criticalLineWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Z S M R Q H C P N =>
      change
        some
          (CriticalLineWitnessUp.mk
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Z))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist S))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
            (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N))) =
          some (CriticalLineWitnessUp.mk Z S M R Q H C P N)
      have hZc :
          CriticalLineWitnessUp.mk
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Z))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist S))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist S))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun Z' =>
            CriticalLineWitnessUp.mk Z'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist S))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist Z)
      have hSc :
          CriticalLineWitnessUp.mk Z
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist S))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun S' =>
            CriticalLineWitnessUp.mk Z S'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist S)
      have hMc :
          CriticalLineWitnessUp.mk Z S
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist M))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun M' =>
            CriticalLineWitnessUp.mk Z S M'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist M)
      have hRc :
          CriticalLineWitnessUp.mk Z S M
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist R))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M R
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun R' =>
            CriticalLineWitnessUp.mk Z S M R'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist R)
      have hQc :
          CriticalLineWitnessUp.mk Z S M R
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist Q))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M R Q
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun Q' =>
            CriticalLineWitnessUp.mk Z S M R Q'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist Q)
      have hHc :
          CriticalLineWitnessUp.mk Z S M R Q
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist H))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M R Q H
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun H' =>
            CriticalLineWitnessUp.mk Z S M R Q H'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist H)
      have hCc :
          CriticalLineWitnessUp.mk Z S M R Q H
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist C))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M R Q H C
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun C' =>
            CriticalLineWitnessUp.mk Z S M R Q H C'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist C)
      have hPc :
          CriticalLineWitnessUp.mk Z S M R Q H C
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist P))
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M R Q H C P
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) :=
        congrArg
          (fun P' =>
            CriticalLineWitnessUp.mk Z S M R Q H C P'
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)))
          (criticalLineWitness_decode_encode_bhist P)
      have hNc :
          CriticalLineWitnessUp.mk Z S M R Q H C P
              (criticalLineWitnessDecodeBHist (criticalLineWitnessEncodeBHist N)) =
            CriticalLineWitnessUp.mk Z S M R Q H C P N :=
        congrArg
          (fun N' => CriticalLineWitnessUp.mk Z S M R Q H C P N')
          (criticalLineWitness_decode_encode_bhist N)
      exact congrArg some
        (Eq.trans hZc
          (Eq.trans hSc
            (Eq.trans hMc
              (Eq.trans hRc
                (Eq.trans hQc
                  (Eq.trans hHc (Eq.trans hCc (Eq.trans hPc hNc))))))))

private theorem criticalLineWitnessToEventFlow_injective
    {x y : CriticalLineWitnessUp} :
    criticalLineWitnessToEventFlow x = criticalLineWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      criticalLineWitnessFromEventFlow (criticalLineWitnessToEventFlow x) =
        criticalLineWitnessFromEventFlow (criticalLineWitnessToEventFlow y) :=
    congrArg criticalLineWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (criticalLineWitness_round_trip x).symm
      (Eq.trans hread (criticalLineWitness_round_trip y)))

private theorem criticalLineWitness_field_faithful :
    ∀ x y : CriticalLineWitnessUp,
      criticalLineWitnessFields x = criticalLineWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Z1 S1 M1 R1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk Z2 S2 M2 R2 Q2 H2 C2 P2 N2 =>
          injection hfields with hZ t1
          injection t1 with hS t2
          injection t2 with hM t3
          injection t3 with hR t4
          injection t4 with hQ t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hZ
          cases hS
          cases hM
          cases hR
          cases hQ
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance criticalLineWitnessBHistCarrier :
    BHistCarrier CriticalLineWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := criticalLineWitnessToEventFlow
  fromEventFlow := criticalLineWitnessFromEventFlow

instance criticalLineWitnessChapterTasteGate :
    ChapterTasteGate CriticalLineWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change criticalLineWitnessFromEventFlow (criticalLineWitnessToEventFlow x) = some x
    exact criticalLineWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (criticalLineWitnessToEventFlow_injective heq)

instance criticalLineWitnessFieldFaithful :
    FieldFaithful CriticalLineWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := criticalLineWitnessFields
  field_faithful := criticalLineWitness_field_faithful

instance criticalLineWitnessNontrivial :
    Nontrivial CriticalLineWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CriticalLineWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CriticalLineWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CriticalLineWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  criticalLineWitnessChapterTasteGate

theorem CriticalLineWitnessTasteGate_single_carrier_alignment :
    forall Z S M R Q H C P N : BHist,
      criticalLineWitnessFields (CriticalLineWitnessUp.mk Z S M R Q H C P N) =
        [Z, S, M, R, Q, H, C, P, N] ∧
      criticalLineWitnessToEventFlow (CriticalLineWitnessUp.mk Z S M R Q H C P N) =
        [[BMark.b1, BMark.b1, BMark.b0],
          criticalLineWitnessEncodeBHist Z,
          criticalLineWitnessEncodeBHist S,
          criticalLineWitnessEncodeBHist M,
          criticalLineWitnessEncodeBHist R,
          criticalLineWitnessEncodeBHist Q,
          criticalLineWitnessEncodeBHist H,
          criticalLineWitnessEncodeBHist C,
          criticalLineWitnessEncodeBHist P,
          criticalLineWitnessEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  intro Z S M R Q H C P N
  exact ⟨rfl, rfl⟩

end BEDC.Derived.CriticalLineWitnessUp
