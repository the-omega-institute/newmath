import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyCompletionFunctorUp : Type where
  | mk (U L G S R E H C P N : BHist) : LocatedCauchyCompletionFunctorUp
  deriving DecidableEq

def locatedCauchyCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyCompletionFunctorEncodeBHist h

def locatedCauchyCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyCompletionFunctorDecodeBHist tail)

private theorem LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCauchyCompletionFunctorDecodeBHist
        (locatedCauchyCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyCompletionFunctorFields :
    LocatedCauchyCompletionFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyCompletionFunctorUp.mk U L G S R E H C P N =>
      [U, L, G, S, R, E, H, C, P, N]

def locatedCauchyCompletionFunctorToEventFlow :
    LocatedCauchyCompletionFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchyCompletionFunctorFields x).map locatedCauchyCompletionFunctorEncodeBHist

private def locatedCauchyCompletionFunctorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCauchyCompletionFunctorEventAtDefault index rest

def locatedCauchyCompletionFunctorFromEventFlow :
    EventFlow → Option LocatedCauchyCompletionFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatedCauchyCompletionFunctorUp.mk
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 0 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 1 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 2 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 3 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 4 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 5 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 6 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 7 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 8 ef))
          (locatedCauchyCompletionFunctorDecodeBHist
            (locatedCauchyCompletionFunctorEventAtDefault 9 ef)))

private theorem LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCauchyCompletionFunctorUp,
      locatedCauchyCompletionFunctorFromEventFlow
          (locatedCauchyCompletionFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U L G S R E H C P N =>
      change
        some
          (LocatedCauchyCompletionFunctorUp.mk
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist U))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist L))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist G))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist S))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist R))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist E))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist H))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist C))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist P))
            (locatedCauchyCompletionFunctorDecodeBHist
              (locatedCauchyCompletionFunctorEncodeBHist N))) =
          some (LocatedCauchyCompletionFunctorUp.mk U L G S R E H C P N)
      rw [LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode U,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode L,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode G,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode S,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode E,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCauchyCompletionFunctorToEventFlow_injective
    {x y : LocatedCauchyCompletionFunctorUp} :
    locatedCauchyCompletionFunctorToEventFlow x =
        locatedCauchyCompletionFunctorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyCompletionFunctorFromEventFlow
          (locatedCauchyCompletionFunctorToEventFlow x) =
        locatedCauchyCompletionFunctorFromEventFlow
          (locatedCauchyCompletionFunctorToEventFlow y) :=
    congrArg locatedCauchyCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedCauchyCompletionFunctorUp,
      locatedCauchyCompletionFunctorFields x = locatedCauchyCompletionFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 L1 G1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 L2 G2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedCauchyCompletionFunctorBHistCarrier :
    BHistCarrier LocatedCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyCompletionFunctorToEventFlow
  fromEventFlow := locatedCauchyCompletionFunctorFromEventFlow

instance locatedCauchyCompletionFunctorChapterTasteGate :
    ChapterTasteGate LocatedCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyCompletionFunctorFromEventFlow
          (locatedCauchyCompletionFunctorToEventFlow x) =
        some x
    exact LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyCompletionFunctorToEventFlow_injective heq)

instance locatedCauchyCompletionFunctorFieldFaithful :
    FieldFaithful LocatedCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCauchyCompletionFunctorFields
  field_faithful := LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_fields

instance locatedCauchyCompletionFunctorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCauchyCompletionFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCauchyCompletionFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCauchyCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCauchyCompletionFunctorChapterTasteGate

theorem LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedCauchyCompletionFunctorUp) ∧
      Nonempty (FieldFaithful LocatedCauchyCompletionFunctorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedCauchyCompletionFunctorUp) ∧
      (∀ h : BHist,
        locatedCauchyCompletionFunctorDecodeBHist
          (locatedCauchyCompletionFunctorEncodeBHist h) = h) ∧
      (∀ x : LocatedCauchyCompletionFunctorUp,
        locatedCauchyCompletionFunctorFromEventFlow
            (locatedCauchyCompletionFunctorToEventFlow x) =
          some x) ∧
      (∀ x y : LocatedCauchyCompletionFunctorUp,
        locatedCauchyCompletionFunctorToEventFlow x =
            locatedCauchyCompletionFunctorToEventFlow y →
          x = y) ∧
      locatedCauchyCompletionFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨locatedCauchyCompletionFunctorChapterTasteGate⟩,
      ⟨locatedCauchyCompletionFunctorFieldFaithful⟩,
      ⟨locatedCauchyCompletionFunctorNontrivial⟩,
      LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode,
      LocatedCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LocatedCauchyCompletionFunctorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCauchyCompletionFunctorUp
