import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterLocatedRealExtractionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterLocatedRealExtractionUp : Type where
  | mk (F L S Q D R T C P N : BHist) : CauchyFilterLocatedRealExtractionUp
  deriving DecidableEq

def CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist h

def CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fields :
    CauchyFilterLocatedRealExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterLocatedRealExtractionUp.mk F L S Q D R T C P N =>
      [F, L, S, Q, D, R, T, C, P, N]

def CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow :
    CauchyFilterLocatedRealExtractionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fields x).map
      CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist

private def CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt index rest

def CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyFilterLocatedRealExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyFilterLocatedRealExtractionUp.mk
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 0 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 1 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 2 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 3 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 4 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 5 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 6 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 7 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 8 ef))
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterLocatedRealExtractionUp,
      CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F L S Q D R T C P N =>
      change
        some
          (CauchyFilterLocatedRealExtractionUp.mk
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist F))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist L))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist S))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist Q))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist T))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyFilterLocatedRealExtractionUp.mk F L S Q D R T C P N)
      rw [CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode F,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode L,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode T,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterLocatedRealExtractionUp} :
    CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_round_trip y)))

instance CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyFilterLocatedRealExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow :=
    CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow :=
    CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyFilterLocatedRealExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyFilterLocatedRealExtractionUp) ∧
      Nonempty (ChapterTasteGate CauchyFilterLocatedRealExtractionUp) ∧
        ∃ route : BHist, Cont BHist.Empty BHist.Empty route ∧ hsame route BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ChapterTasteGate
  exact
    ⟨Nonempty.intro
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_BHistCarrier,
      Nonempty.intro
        CauchyFilterLocatedRealExtractionTasteGate_single_carrier_alignment_ChapterTasteGate,
      BHist.Empty, rfl, hsame_refl BHist.Empty⟩

end BEDC.Derived.CauchyFilterLocatedRealExtractionUp
