import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealCompletionUniversalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealCompletionUniversalUp : Type where
  | mk (D S R E L F X Q H C P N : BHist) : LocatedRealCompletionUniversalUp
  deriving DecidableEq

def locatedRealCompletionUniversalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealCompletionUniversalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealCompletionUniversalEncodeBHist h

def locatedRealCompletionUniversalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealCompletionUniversalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealCompletionUniversalDecodeBHist tail)

private theorem LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealCompletionUniversalFields :
    LocatedRealCompletionUniversalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealCompletionUniversalUp.mk D S R E L F X Q H C P N =>
      [D, S, R, E, L, F, X, Q, H, C, P, N]

def locatedRealCompletionUniversalToEventFlow :
    LocatedRealCompletionUniversalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedRealCompletionUniversalFields x).map
    locatedRealCompletionUniversalEncodeBHist

private def locatedRealCompletionUniversalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealCompletionUniversalEventAtDefault index rest

def locatedRealCompletionUniversalFromEventFlow
    (ef : EventFlow) : Option LocatedRealCompletionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealCompletionUniversalUp.mk
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 0 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 1 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 2 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 3 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 4 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 5 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 6 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 7 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 8 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 9 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 10 ef))
      (locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEventAtDefault 11 ef)))

private theorem LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealCompletionUniversalUp,
      locatedRealCompletionUniversalFromEventFlow
        (locatedRealCompletionUniversalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E L F X Q H C P N =>
      change
        some
          (LocatedRealCompletionUniversalUp.mk
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist D))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist S))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist R))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist E))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist L))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist F))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist X))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist Q))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist H))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist C))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist P))
            (locatedRealCompletionUniversalDecodeBHist
              (locatedRealCompletionUniversalEncodeBHist N))) =
          some (LocatedRealCompletionUniversalUp.mk D S R E L F X Q H C P N)
      rw [LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode D,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode S,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode R,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode E,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode L,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode F,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode X,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode Q,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode H,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode C,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode P,
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode N]

private theorem LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealCompletionUniversalUp} :
    locatedRealCompletionUniversalToEventFlow x =
      locatedRealCompletionUniversalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealCompletionUniversalFromEventFlow
          (locatedRealCompletionUniversalToEventFlow x) =
        locatedRealCompletionUniversalFromEventFlow
          (locatedRealCompletionUniversalToEventFlow y) :=
    congrArg locatedRealCompletionUniversalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedRealCompletionUniversalUp,
      locatedRealCompletionUniversalFields x = locatedRealCompletionUniversalFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 E1 L1 F1 X1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 E2 L2 F2 X2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealCompletionUniversalBHistCarrier :
    BHistCarrier LocatedRealCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealCompletionUniversalToEventFlow
  fromEventFlow := locatedRealCompletionUniversalFromEventFlow

instance locatedRealCompletionUniversalChapterTasteGate :
    ChapterTasteGate LocatedRealCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealCompletionUniversalFromEventFlow
        (locatedRealCompletionUniversalToEventFlow x) = some x
    exact LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealCompletionUniversalFieldFaithful :
    FieldFaithful LocatedRealCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealCompletionUniversalFields
  field_faithful := LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_fields

instance locatedRealCompletionUniversalNontrivial :
    Nontrivial LocatedRealCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealCompletionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LocatedRealCompletionUniversalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealCompletionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealCompletionUniversalChapterTasteGate

theorem LocatedRealCompletionUniversalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealCompletionUniversalDecodeBHist
        (locatedRealCompletionUniversalEncodeBHist h) = h) ∧
      (∀ x : LocatedRealCompletionUniversalUp,
        locatedRealCompletionUniversalFromEventFlow
          (locatedRealCompletionUniversalToEventFlow x) = some x) ∧
        (∀ x y : LocatedRealCompletionUniversalUp,
          locatedRealCompletionUniversalToEventFlow x =
            locatedRealCompletionUniversalToEventFlow y → x = y) ∧
          locatedRealCompletionUniversalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_decode,
      LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedRealCompletionUniversalTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealCompletionUniversalUp
