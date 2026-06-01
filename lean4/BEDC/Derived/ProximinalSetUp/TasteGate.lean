import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProximinalSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProximinalSetUp : Type where
  | mk (X L D W E H C P N : BHist) : ProximinalSetUp
  deriving DecidableEq

def proximinalSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proximinalSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proximinalSetEncodeBHist h

def proximinalSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proximinalSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proximinalSetDecodeBHist tail)

private theorem ProximinalSetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, proximinalSetDecodeBHist (proximinalSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def proximinalSetFields : ProximinalSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProximinalSetUp.mk X L D W E H C P N => [X, L, D, W, E, H, C, P, N]

def proximinalSetToEventFlow : ProximinalSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun token => (proximinalSetFields token).map proximinalSetEncodeBHist

private def proximinalSetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => proximinalSetEventAtDefault index rest

def proximinalSetFromEventFlow (ef : EventFlow) : Option ProximinalSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProximinalSetUp.mk
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 0 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 1 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 2 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 3 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 4 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 5 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 6 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 7 ef))
      (proximinalSetDecodeBHist (proximinalSetEventAtDefault 8 ef)))

private theorem ProximinalSetTasteGate_single_carrier_alignment_round_trip :
    ∀ token : ProximinalSetUp,
      proximinalSetFromEventFlow (proximinalSetToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X L D W E H C P N =>
      change
        some
          (ProximinalSetUp.mk
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist X))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist L))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist D))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist W))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist E))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist H))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist C))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist P))
            (proximinalSetDecodeBHist (proximinalSetEncodeBHist N))) =
          some (ProximinalSetUp.mk X L D W E H C P N)
      rw [ProximinalSetTasteGate_single_carrier_alignment_decode X,
        ProximinalSetTasteGate_single_carrier_alignment_decode L,
        ProximinalSetTasteGate_single_carrier_alignment_decode D,
        ProximinalSetTasteGate_single_carrier_alignment_decode W,
        ProximinalSetTasteGate_single_carrier_alignment_decode E,
        ProximinalSetTasteGate_single_carrier_alignment_decode H,
        ProximinalSetTasteGate_single_carrier_alignment_decode C,
        ProximinalSetTasteGate_single_carrier_alignment_decode P,
        ProximinalSetTasteGate_single_carrier_alignment_decode N]

private theorem ProximinalSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProximinalSetUp} :
    proximinalSetToEventFlow x = proximinalSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proximinalSetFromEventFlow (proximinalSetToEventFlow x) =
        proximinalSetFromEventFlow (proximinalSetToEventFlow y) :=
    congrArg proximinalSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProximinalSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProximinalSetTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProximinalSetTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProximinalSetUp, proximinalSetFields x = proximinalSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro a b hfields
  cases a with
  | mk X1 L1 D1 W1 E1 H1 C1 P1 N1 =>
      cases b with
      | mk X2 L2 D2 W2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance proximinalSetBHistCarrier : BHistCarrier ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proximinalSetToEventFlow
  fromEventFlow := proximinalSetFromEventFlow

instance proximinalSetChapterTasteGate : ChapterTasteGate ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proximinalSetFromEventFlow (proximinalSetToEventFlow x) = some x
    exact ProximinalSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProximinalSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance proximinalSetFieldFaithful : FieldFaithful ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := proximinalSetFields
  field_faithful := ProximinalSetTasteGate_single_carrier_alignment_fields

instance proximinalSetNontrivial : Nontrivial ProximinalSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProximinalSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProximinalSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProximinalSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proximinalSetChapterTasteGate

theorem ProximinalSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, proximinalSetDecodeBHist (proximinalSetEncodeBHist h) = h) ∧
      (∀ x : ProximinalSetUp,
        proximinalSetFromEventFlow (proximinalSetToEventFlow x) = some x) ∧
        (∀ x y : ProximinalSetUp,
          proximinalSetToEventFlow x = proximinalSetToEventFlow y → x = y) ∧
          proximinalSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ProximinalSetTasteGate_single_carrier_alignment_decode,
      ProximinalSetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ProximinalSetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ProximinalSetUp
