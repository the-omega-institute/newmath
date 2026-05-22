import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyCompactUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyCompactUp : Type where
  | mk (X x r B K A H C P N : BHist) : LocallyCompactUp
  deriving DecidableEq

def locallyCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyCompactEncodeBHist h

def locallyCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyCompactDecodeBHist tail)

private theorem locallyCompact_decode_encode_bhist :
    ∀ h : BHist, locallyCompactDecodeBHist (locallyCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locallyCompactFields : LocallyCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyCompactUp.mk X x r B K A H C P N => [X, x, r, B, K, A, H, C, P, N]

def locallyCompactToEventFlow : LocallyCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locallyCompactFields x).map locallyCompactEncodeBHist

private def locallyCompactEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locallyCompactEventAtDefault index rest

def locallyCompactFromEventFlow (ef : EventFlow) : Option LocallyCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocallyCompactUp.mk
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 0 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 1 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 2 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 3 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 4 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 5 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 6 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 7 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 8 ef))
      (locallyCompactDecodeBHist (locallyCompactEventAtDefault 9 ef)))

private theorem locallyCompact_round_trip :
    ∀ x : LocallyCompactUp,
      locallyCompactFromEventFlow (locallyCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X x r B K A H C P N =>
      change
        some
          (LocallyCompactUp.mk
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist X))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist x))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist r))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist B))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist K))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist A))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist H))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist C))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist P))
            (locallyCompactDecodeBHist (locallyCompactEncodeBHist N))) =
          some (LocallyCompactUp.mk X x r B K A H C P N)
      rw [locallyCompact_decode_encode_bhist X,
        locallyCompact_decode_encode_bhist x,
        locallyCompact_decode_encode_bhist r,
        locallyCompact_decode_encode_bhist B,
        locallyCompact_decode_encode_bhist K,
        locallyCompact_decode_encode_bhist A,
        locallyCompact_decode_encode_bhist H,
        locallyCompact_decode_encode_bhist C,
        locallyCompact_decode_encode_bhist P,
        locallyCompact_decode_encode_bhist N]

private theorem locallyCompactToEventFlow_injective {x y : LocallyCompactUp} :
    locallyCompactToEventFlow x = locallyCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locallyCompactFromEventFlow (locallyCompactToEventFlow x) =
        locallyCompactFromEventFlow (locallyCompactToEventFlow y) :=
    congrArg locallyCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locallyCompact_round_trip x).symm
      (Eq.trans hread (locallyCompact_round_trip y)))

private theorem locallyCompact_fields_faithful :
    ∀ x y : LocallyCompactUp, locallyCompactFields x = locallyCompactFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 x1 r1 B1 K1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 x2 r2 B2 K2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locallyCompactBHistCarrier : BHistCarrier LocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locallyCompactToEventFlow
  fromEventFlow := locallyCompactFromEventFlow

instance locallyCompactChapterTasteGate : ChapterTasteGate LocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locallyCompactFromEventFlow (locallyCompactToEventFlow x) = some x
    exact locallyCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locallyCompactToEventFlow_injective heq)

instance locallyCompactFieldFaithful : FieldFaithful LocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locallyCompactFields
  field_faithful := locallyCompact_fields_faithful

instance locallyCompactNontrivial : Nontrivial LocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocallyCompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocallyCompactUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocallyCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locallyCompactChapterTasteGate

theorem LocallyCompactTasteGate_single_carrier_alignment :
    (∀ h : BHist, locallyCompactDecodeBHist (locallyCompactEncodeBHist h) = h) ∧
      (∀ x : LocallyCompactUp,
        locallyCompactFromEventFlow (locallyCompactToEventFlow x) = some x) ∧
        (∀ x y : LocallyCompactUp,
          locallyCompactToEventFlow x = locallyCompactToEventFlow y → x = y) ∧
          locallyCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨locallyCompact_decode_encode_bhist,
      locallyCompact_round_trip,
      (fun _ _ heq => locallyCompactToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocallyCompactUp.TasteGate

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived.LocallyCompactUp.TasteGate

theorem LocallyCompactUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocallyCompactUp) ∧
      Nonempty (FieldFaithful LocallyCompactUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocallyCompactUp) ∧
      (∀ h : BHist, locallyCompactDecodeBHist (locallyCompactEncodeBHist h) = h) ∧
      (∀ x : LocallyCompactUp,
        locallyCompactFromEventFlow (locallyCompactToEventFlow x) = some x) ∧
        (∀ x y : LocallyCompactUp,
          locallyCompactToEventFlow x = locallyCompactToEventFlow y → x = y) ∧
          locallyCompactEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨locallyCompactChapterTasteGate⟩,
      ⟨locallyCompactFieldFaithful⟩,
      ⟨locallyCompactNontrivial⟩,
      LocallyCompactTasteGate_single_carrier_alignment.1,
      LocallyCompactTasteGate_single_carrier_alignment.2.1,
      LocallyCompactTasteGate_single_carrier_alignment.2.2.1,
      LocallyCompactTasteGate_single_carrier_alignment.2.2.2⟩

end BEDC.Derived.LocallyCompactUp
