import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LogicContradictionMetaLoopUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LogicContradictionMetaLoopUp : Type where
  | mk : (P R M A T C G N : BHist) → LogicContradictionMetaLoopUp
  deriving DecidableEq

def logicContradictionMetaLoopEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: logicContradictionMetaLoopEncodeBHist h
  | BHist.e1 h => BMark.b1 :: logicContradictionMetaLoopEncodeBHist h

def logicContradictionMetaLoopDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (logicContradictionMetaLoopDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (logicContradictionMetaLoopDecodeBHist tail)

private theorem LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      logicContradictionMetaLoopDecodeBHist
        (logicContradictionMetaLoopEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def logicContradictionMetaLoopFields : LogicContradictionMetaLoopUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LogicContradictionMetaLoopUp.mk P R M A T C G N => [P, R, M, A, T, C, G, N]

def logicContradictionMetaLoopToEventFlow : LogicContradictionMetaLoopUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LogicContradictionMetaLoopUp.mk P R M A T C G N =>
      [[BMark.b0],
        logicContradictionMetaLoopEncodeBHist P,
        [BMark.b1, BMark.b0],
        logicContradictionMetaLoopEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        logicContradictionMetaLoopEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        logicContradictionMetaLoopEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        logicContradictionMetaLoopEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        logicContradictionMetaLoopEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        logicContradictionMetaLoopEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        logicContradictionMetaLoopEncodeBHist N]

private def LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault index rest

def logicContradictionMetaLoopFromEventFlow
    (ef : EventFlow) : Option LogicContradictionMetaLoopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LogicContradictionMetaLoopUp.mk
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (logicContradictionMetaLoopDecodeBHist
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_eventAtDefault 15 ef)))

private theorem LogicContradictionMetaLoopTasteGate_single_carrier_alignment_mk_congr
    {P P' R R' M M' A A' T T' C C' G G' N N' : BHist} :
    P = P' →
      R = R' →
        M = M' →
          A = A' →
            T = T' →
              C = C' →
                G = G' →
                  N = N' →
                    LogicContradictionMetaLoopUp.mk P R M A T C G N =
                      LogicContradictionMetaLoopUp.mk P' R' M' A' T' C' G' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hP hR hM hA hT hC hG hN
  cases hP
  cases hR
  cases hM
  cases hA
  cases hT
  cases hC
  cases hG
  cases hN
  rfl

private theorem LogicContradictionMetaLoopTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LogicContradictionMetaLoopUp,
      logicContradictionMetaLoopFromEventFlow
        (logicContradictionMetaLoopToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P R M A T C G N =>
      change
        some
          (LogicContradictionMetaLoopUp.mk
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist P))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist R))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist M))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist A))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist T))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist C))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist G))
            (logicContradictionMetaLoopDecodeBHist
              (logicContradictionMetaLoopEncodeBHist N))) =
          some (LogicContradictionMetaLoopUp.mk P R M A T C G N)
      have hP := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode P
      have hR := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode R
      have hM := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode M
      have hA := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode A
      have hT := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode T
      have hC := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode C
      have hG := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode G
      have hN := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode N
      have hmk :=
        LogicContradictionMetaLoopTasteGate_single_carrier_alignment_mk_congr
          hP hR hM hA hT hC hG hN
      exact congrArg Option.some hmk

private theorem LogicContradictionMetaLoopTasteGate_single_carrier_alignment_injective
    {x y : LogicContradictionMetaLoopUp} :
    logicContradictionMetaLoopToEventFlow x =
      logicContradictionMetaLoopToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      logicContradictionMetaLoopFromEventFlow (logicContradictionMetaLoopToEventFlow x) =
        logicContradictionMetaLoopFromEventFlow (logicContradictionMetaLoopToEventFlow y) :=
    congrArg logicContradictionMetaLoopFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_round_trip y)))

private theorem LogicContradictionMetaLoopTasteGate_single_carrier_alignment_fields :
    ∀ x y : LogicContradictionMetaLoopUp,
      logicContradictionMetaLoopFields x = logicContradictionMetaLoopFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 R1 M1 A1 T1 C1 G1 N1 =>
      cases y with
      | mk P2 R2 M2 A2 T2 C2 G2 N2 =>
          cases hfields
          rfl

instance logicContradictionMetaLoopBHistCarrier :
    BHistCarrier LogicContradictionMetaLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := logicContradictionMetaLoopToEventFlow
  fromEventFlow := logicContradictionMetaLoopFromEventFlow

instance logicContradictionMetaLoopChapterTasteGate :
    ChapterTasteGate LogicContradictionMetaLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      logicContradictionMetaLoopFromEventFlow
        (logicContradictionMetaLoopToEventFlow x) = some x
    exact LogicContradictionMetaLoopTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LogicContradictionMetaLoopTasteGate_single_carrier_alignment_injective heq)

instance logicContradictionMetaLoopFieldFaithful :
    FieldFaithful LogicContradictionMetaLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := logicContradictionMetaLoopFields
  field_faithful := LogicContradictionMetaLoopTasteGate_single_carrier_alignment_fields

instance logicContradictionMetaLoopNontrivial : Nontrivial LogicContradictionMetaLoopUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LogicContradictionMetaLoopUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LogicContradictionMetaLoopUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LogicContradictionMetaLoopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  logicContradictionMetaLoopChapterTasteGate

theorem LogicContradictionMetaLoopTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      logicContradictionMetaLoopDecodeBHist
        (logicContradictionMetaLoopEncodeBHist h) = h) ∧
      (∀ x : LogicContradictionMetaLoopUp,
        logicContradictionMetaLoopFromEventFlow
          (logicContradictionMetaLoopToEventFlow x) = some x) ∧
        (∀ x y : LogicContradictionMetaLoopUp,
          logicContradictionMetaLoopToEventFlow x =
            logicContradictionMetaLoopToEventFlow y → x = y) ∧
          logicContradictionMetaLoopEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LogicContradictionMetaLoopTasteGate_single_carrier_alignment_decode
  · constructor
    · exact LogicContradictionMetaLoopTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact LogicContradictionMetaLoopTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.LogicContradictionMetaLoopUp
