import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicBracketApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicBracketApproximationUp : Type where
  | mk (L U Q I S W R E H C P N : BHist) : DyadicBracketApproximationUp
  deriving DecidableEq

def dyadicBracketApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBracketApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBracketApproximationEncodeBHist h

def dyadicBracketApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBracketApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBracketApproximationDecodeBHist tail)

private theorem DyadicBracketApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicBracketApproximationFields : DyadicBracketApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicBracketApproximationUp.mk L U Q I S W R E H C P N =>
      [L, U, Q, I, S, W, R, E, H, C, P, N]

def dyadicBracketApproximationToEventFlow : DyadicBracketApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicBracketApproximationFields x).map dyadicBracketApproximationEncodeBHist

private def dyadicBracketApproximationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicBracketApproximationEventAtDefault index rest

def dyadicBracketApproximationFromEventFlow :
    EventFlow → Option DyadicBracketApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (DyadicBracketApproximationUp.mk
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 0 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 1 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 2 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 3 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 4 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 5 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 6 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 7 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 8 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 9 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 10 ef))
        (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEventAtDefault 11 ef)))

private theorem DyadicBracketApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicBracketApproximationUp,
      dyadicBracketApproximationFromEventFlow (dyadicBracketApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U Q I S W R E H C P N =>
      change
        some
          (DyadicBracketApproximationUp.mk
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist L))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist U))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist Q))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist I))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist S))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist W))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist R))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist E))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist H))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist C))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist P))
            (dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist N))) =
          some (DyadicBracketApproximationUp.mk L U Q I S W R E H C P N)
      rw [DyadicBracketApproximationTasteGate_single_carrier_alignment_decode L,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode U,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode Q,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode I,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode S,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode W,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode R,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode E,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode H,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode C,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode P,
        DyadicBracketApproximationTasteGate_single_carrier_alignment_decode N]

private theorem DyadicBracketApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicBracketApproximationUp} :
    dyadicBracketApproximationToEventFlow x = dyadicBracketApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicBracketApproximationFromEventFlow (dyadicBracketApproximationToEventFlow x) =
        dyadicBracketApproximationFromEventFlow (dyadicBracketApproximationToEventFlow y) :=
    congrArg dyadicBracketApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicBracketApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicBracketApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicBracketApproximationTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicBracketApproximationUp,
      dyadicBracketApproximationFields x = dyadicBracketApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 Q1 I1 S1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 Q2 I2 S2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicBracketApproximationBHistCarrier :
    BHistCarrier DyadicBracketApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBracketApproximationToEventFlow
  fromEventFlow := dyadicBracketApproximationFromEventFlow

instance dyadicBracketApproximationChapterTasteGate :
    ChapterTasteGate DyadicBracketApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicBracketApproximationFromEventFlow (dyadicBracketApproximationToEventFlow x) =
        some x
    exact DyadicBracketApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicBracketApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicBracketApproximationFieldFaithful :
    FieldFaithful DyadicBracketApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicBracketApproximationFields
  field_faithful := DyadicBracketApproximationTasteGate_single_carrier_alignment_fields

instance dyadicBracketApproximationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicBracketApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicBracketApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DyadicBracketApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicBracketApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicBracketApproximationChapterTasteGate

theorem DyadicBracketApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicBracketApproximationUp) ∧
      Nonempty (FieldFaithful DyadicBracketApproximationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicBracketApproximationUp) ∧
          (∀ h : BHist,
            dyadicBracketApproximationDecodeBHist (dyadicBracketApproximationEncodeBHist h) = h) ∧
            (∀ x : DyadicBracketApproximationUp,
              dyadicBracketApproximationFromEventFlow
                  (dyadicBracketApproximationToEventFlow x) =
                some x) ∧
              (∀ x y : DyadicBracketApproximationUp,
                dyadicBracketApproximationToEventFlow x =
                    dyadicBracketApproximationToEventFlow y →
                  x = y) ∧
                dyadicBracketApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicBracketApproximationChapterTasteGate⟩,
      ⟨dyadicBracketApproximationFieldFaithful⟩,
      ⟨dyadicBracketApproximationNontrivial⟩,
      DyadicBracketApproximationTasteGate_single_carrier_alignment_decode,
      DyadicBracketApproximationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicBracketApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicBracketApproximationUp
