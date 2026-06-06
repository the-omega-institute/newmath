import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealContinuityUp : Type where
  | mk (X D W R M E H C P N : BHist) : LocatedRealContinuityUp
  deriving DecidableEq

def locatedRealContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealContinuityEncodeBHist h

def locatedRealContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealContinuityDecodeBHist tail)

private theorem locatedRealContinuityDecode_encode :
    ∀ h : BHist,
      locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealContinuityFields : LocatedRealContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealContinuityUp.mk X D W R M E H C P N => [X, D, W, R, M, E, H, C, P, N]

def locatedRealContinuityToEventFlow : LocatedRealContinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedRealContinuityFields x).map locatedRealContinuityEncodeBHist

private def locatedRealContinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealContinuityEventAtDefault index rest

def locatedRealContinuityFromEventFlow (ef : EventFlow) : Option LocatedRealContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealContinuityUp.mk
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 0 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 1 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 2 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 3 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 4 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 5 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 6 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 7 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 8 ef))
      (locatedRealContinuityDecodeBHist (locatedRealContinuityEventAtDefault 9 ef)))

private theorem locatedRealContinuity_round_trip (x : LocatedRealContinuityUp) :
    locatedRealContinuityFromEventFlow (locatedRealContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X D W R M E H C P N =>
      change
        some
          (LocatedRealContinuityUp.mk
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist X))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist D))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist W))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist R))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist M))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist E))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist H))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist C))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist P))
            (locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist N))) =
          some (LocatedRealContinuityUp.mk X D W R M E H C P N)
      rw [locatedRealContinuityDecode_encode X, locatedRealContinuityDecode_encode D,
        locatedRealContinuityDecode_encode W, locatedRealContinuityDecode_encode R,
        locatedRealContinuityDecode_encode M, locatedRealContinuityDecode_encode E,
        locatedRealContinuityDecode_encode H, locatedRealContinuityDecode_encode C,
        locatedRealContinuityDecode_encode P, locatedRealContinuityDecode_encode N]

private theorem locatedRealContinuityToEventFlow_injective
    {x y : LocatedRealContinuityUp} :
    locatedRealContinuityToEventFlow x = locatedRealContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealContinuityFromEventFlow (locatedRealContinuityToEventFlow x) =
        locatedRealContinuityFromEventFlow (locatedRealContinuityToEventFlow y) :=
    congrArg locatedRealContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealContinuity_round_trip x).symm
      (Eq.trans hread (locatedRealContinuity_round_trip y)))

private theorem locatedRealContinuity_field_faithful :
    ∀ x y : LocatedRealContinuityUp,
      locatedRealContinuityFields x = locatedRealContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 D1 W1 R1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 D2 W2 R2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealContinuityBHistCarrier : BHistCarrier LocatedRealContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealContinuityToEventFlow
  fromEventFlow := locatedRealContinuityFromEventFlow

instance locatedRealContinuityChapterTasteGate : ChapterTasteGate LocatedRealContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealContinuityFromEventFlow (locatedRealContinuityToEventFlow x) = some x
    exact locatedRealContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealContinuityToEventFlow_injective heq)

instance locatedRealContinuityFieldFaithful : FieldFaithful LocatedRealContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealContinuityFields
  field_faithful := locatedRealContinuity_field_faithful

instance locatedRealContinuityNontrivial : Nontrivial LocatedRealContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealContinuityChapterTasteGate

theorem LocatedRealContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRealContinuityDecodeBHist (locatedRealContinuityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedRealContinuityUp) ∧
        Nonempty (ChapterTasteGate LocatedRealContinuityUp) ∧
          locatedRealContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨locatedRealContinuityDecode_encode,
      ⟨locatedRealContinuityBHistCarrier⟩,
      ⟨locatedRealContinuityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedRealContinuityUp
