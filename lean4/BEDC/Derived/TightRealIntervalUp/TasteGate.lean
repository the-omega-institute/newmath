import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TightRealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TightRealIntervalUp : Type where
  | mk (L U Q D S R E H C P N : BHist) : TightRealIntervalUp
  deriving DecidableEq

def tightRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tightRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tightRealIntervalEncodeBHist h

def tightRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tightRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tightRealIntervalDecodeBHist tail)

private theorem TightRealIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tightRealIntervalFields : TightRealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TightRealIntervalUp.mk L U Q D S R E H C P N =>
      [L, U, Q, D, S, R, E, H, C, P, N]

def tightRealIntervalToEventFlow : TightRealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map tightRealIntervalEncodeBHist (tightRealIntervalFields x)

private def tightRealIntervalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tightRealIntervalEventAt index rest

def tightRealIntervalFromEventFlow : EventFlow → Option TightRealIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (TightRealIntervalUp.mk
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 0 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 1 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 2 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 3 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 4 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 5 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 6 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 7 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 8 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 9 ef))
          (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 10 ef)))

private theorem TightRealIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TightRealIntervalUp,
      tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U Q D S R E H C P N =>
      change
        some
          (TightRealIntervalUp.mk
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist L))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist U))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist Q))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist D))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist S))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist R))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist E))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist H))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist C))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist P))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist N))) =
          some (TightRealIntervalUp.mk L U Q D S R E H C P N)
      rw [TightRealIntervalTasteGate_single_carrier_alignment_decode L,
        TightRealIntervalTasteGate_single_carrier_alignment_decode U,
        TightRealIntervalTasteGate_single_carrier_alignment_decode Q,
        TightRealIntervalTasteGate_single_carrier_alignment_decode D,
        TightRealIntervalTasteGate_single_carrier_alignment_decode S,
        TightRealIntervalTasteGate_single_carrier_alignment_decode R,
        TightRealIntervalTasteGate_single_carrier_alignment_decode E,
        TightRealIntervalTasteGate_single_carrier_alignment_decode H,
        TightRealIntervalTasteGate_single_carrier_alignment_decode C,
        TightRealIntervalTasteGate_single_carrier_alignment_decode P,
        TightRealIntervalTasteGate_single_carrier_alignment_decode N]

private theorem TightRealIntervalTasteGate_single_carrier_alignment_injective
    {x y : TightRealIntervalUp} :
    tightRealIntervalToEventFlow x = tightRealIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow x) =
        tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow y) :=
    congrArg tightRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TightRealIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TightRealIntervalTasteGate_single_carrier_alignment_round_trip y)))

private theorem tightRealIntervalFieldFaithful :
    ∀ x y : TightRealIntervalUp, tightRealIntervalFields x = tightRealIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk L1 U1 Q1 D1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 Q2 D2 S2 R2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance tightRealIntervalBHistCarrier : BHistCarrier TightRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tightRealIntervalToEventFlow
  fromEventFlow := tightRealIntervalFromEventFlow

instance tightRealIntervalChapterTasteGate : ChapterTasteGate TightRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow x) = some x
    exact TightRealIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TightRealIntervalTasteGate_single_carrier_alignment_injective heq)

instance tightRealIntervalFieldFaithfulInstance : FieldFaithful TightRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tightRealIntervalFields
  field_faithful := tightRealIntervalFieldFaithful

instance tightRealIntervalNontrivial : BEDC.Meta.TasteGate.Nontrivial TightRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TightRealIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TightRealIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TightRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tightRealIntervalChapterTasteGate

def taste_gate_witness : FieldFaithful TightRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tightRealIntervalFieldFaithfulInstance

theorem TightRealIntervalTasteGate_single_carrier_alignment :
    tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist BHist.Empty) = BHist.Empty ∧
      (∀ h : BHist, tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨rfl, TightRealIntervalTasteGate_single_carrier_alignment_decode⟩

end BEDC.Derived.TightRealIntervalUp
