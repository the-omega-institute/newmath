import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntervalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntervalUp : Type where
  | mk (L U rho Delta Lambda M Q H C P N : BHist) : LocatedRealIntervalUp
  deriving DecidableEq

def locatedRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntervalEncodeBHist h

def locatedRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntervalDecodeBHist tail)

private theorem locatedRealInterval_decode_encode_bhist :
    ∀ h : BHist, locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealIntervalFields : LocatedRealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntervalUp.mk L U rho Delta Lambda M Q H C P N =>
      [L, U, rho, Delta, Lambda, M, Q, H, C, P, N]

def locatedRealIntervalToEventFlow : LocatedRealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealIntervalFields x).map locatedRealIntervalEncodeBHist

private def locatedRealIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealIntervalEventAtDefault index rest

def locatedRealIntervalFromEventFlow (ef : EventFlow) : Option LocatedRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealIntervalUp.mk
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 0 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 1 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 2 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 3 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 4 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 5 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 6 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 7 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 8 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 9 ef))
      (locatedRealIntervalDecodeBHist (locatedRealIntervalEventAtDefault 10 ef)))

private theorem locatedRealInterval_round_trip :
    ∀ x : LocatedRealIntervalUp,
      locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U rho Delta Lambda M Q H C P N =>
      change
        some
          (LocatedRealIntervalUp.mk
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist L))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist U))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist rho))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist Delta))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist Lambda))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist M))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist Q))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist H))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist C))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist P))
            (locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist N))) =
          some (LocatedRealIntervalUp.mk L U rho Delta Lambda M Q H C P N)
      rw [locatedRealInterval_decode_encode_bhist L,
        locatedRealInterval_decode_encode_bhist U,
        locatedRealInterval_decode_encode_bhist rho,
        locatedRealInterval_decode_encode_bhist Delta,
        locatedRealInterval_decode_encode_bhist Lambda,
        locatedRealInterval_decode_encode_bhist M,
        locatedRealInterval_decode_encode_bhist Q,
        locatedRealInterval_decode_encode_bhist H,
        locatedRealInterval_decode_encode_bhist C,
        locatedRealInterval_decode_encode_bhist P,
        locatedRealInterval_decode_encode_bhist N]

private theorem locatedRealIntervalToEventFlow_injective {x y : LocatedRealIntervalUp} :
    locatedRealIntervalToEventFlow x = locatedRealIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) =
        locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow y) :=
    congrArg locatedRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealInterval_round_trip x).symm
      (Eq.trans hread (locatedRealInterval_round_trip y)))

private theorem locatedRealInterval_fields_faithful :
    ∀ x y : LocatedRealIntervalUp,
      locatedRealIntervalFields x = locatedRealIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 rho1 Delta1 Lambda1 M1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 rho2 Delta2 Lambda2 M2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealIntervalBHistCarrier : BHistCarrier LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealIntervalToEventFlow
  fromEventFlow := locatedRealIntervalFromEventFlow

instance locatedRealIntervalChapterTasteGate : ChapterTasteGate LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) = some x
    exact locatedRealInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealIntervalToEventFlow_injective heq)

instance locatedRealIntervalFieldFaithful : FieldFaithful LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealIntervalFields
  field_faithful := locatedRealInterval_fields_faithful

instance locatedRealIntervalNontrivial : Nontrivial LocatedRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealIntervalChapterTasteGate

theorem LocatedRealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRealIntervalDecodeBHist (locatedRealIntervalEncodeBHist h) = h) ∧
      (∀ x : LocatedRealIntervalUp,
        locatedRealIntervalFromEventFlow (locatedRealIntervalToEventFlow x) = some x) ∧
        (∀ x y : LocatedRealIntervalUp,
          locatedRealIntervalToEventFlow x = locatedRealIntervalToEventFlow y → x = y) ∧
          locatedRealIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨locatedRealInterval_decode_encode_bhist,
      locatedRealInterval_round_trip,
      (fun _ _ heq => locatedRealIntervalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealIntervalUp.TasteGate

namespace BEDC.Derived.LocatedRealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem LocatedRealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.locatedRealIntervalDecodeBHist
          (TasteGate.locatedRealIntervalEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.LocatedRealIntervalUp,
        TasteGate.locatedRealIntervalFromEventFlow
            (TasteGate.locatedRealIntervalToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.LocatedRealIntervalUp,
          TasteGate.locatedRealIntervalToEventFlow x =
              TasteGate.locatedRealIntervalToEventFlow y →
            x = y) ∧
          TasteGate.locatedRealIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact TasteGate.LocatedRealIntervalTasteGate_single_carrier_alignment

end BEDC.Derived.LocatedRealIntervalUp
