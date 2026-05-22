import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannStieltjesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannStieltjesUp : Type where
  | mk (F A T S I E H C P N : BHist) : RiemannStieltjesUp
  deriving DecidableEq

def riemannStieltjesEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannStieltjesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannStieltjesEncodeBHist h

def riemannStieltjesDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannStieltjesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannStieltjesDecodeBHist tail)

private theorem RiemannStieltjesUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def riemannStieltjesFields : RiemannStieltjesUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannStieltjesUp.mk F A T S I E H C P N => [F, A, T, S, I, E, H, C, P, N]

def riemannStieltjesToEventFlow : RiemannStieltjesUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannStieltjesFields x).map riemannStieltjesEncodeBHist

private def riemannStieltjesEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannStieltjesEventAtDefault index rest

def riemannStieltjesFromEventFlow (ef : EventFlow) : Option RiemannStieltjesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannStieltjesUp.mk
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 0 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 1 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 2 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 3 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 4 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 5 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 6 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 7 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 8 ef))
      (riemannStieltjesDecodeBHist (riemannStieltjesEventAtDefault 9 ef)))

private theorem RiemannStieltjesUpTasteGate_single_carrier_alignment_round_trip :
    forall x : RiemannStieltjesUp,
      riemannStieltjesFromEventFlow (riemannStieltjesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F A T S I E H C P N =>
      change
        some
          (RiemannStieltjesUp.mk
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist F))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist A))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist T))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist S))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist I))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist E))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist H))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist C))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist P))
            (riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist N))) =
          some (RiemannStieltjesUp.mk F A T S I E H C P N)
      rw [RiemannStieltjesUpTasteGate_single_carrier_alignment_decode F,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode A,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode T,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode S,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode I,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode E,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode H,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode C,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode P,
        RiemannStieltjesUpTasteGate_single_carrier_alignment_decode N]

private theorem RiemannStieltjesUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannStieltjesUp} :
    riemannStieltjesToEventFlow x = riemannStieltjesToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannStieltjesFromEventFlow (riemannStieltjesToEventFlow x) =
        riemannStieltjesFromEventFlow (riemannStieltjesToEventFlow y) :=
    congrArg riemannStieltjesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannStieltjesUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannStieltjesUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RiemannStieltjesUpTasteGate_single_carrier_alignment_fields :
    forall x y : RiemannStieltjesUp, riemannStieltjesFields x = riemannStieltjesFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 A1 T1 S1 I1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 A2 T2 S2 I2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance riemannStieltjesBHistCarrier : BHistCarrier RiemannStieltjesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannStieltjesToEventFlow
  fromEventFlow := riemannStieltjesFromEventFlow

instance riemannStieltjesChapterTasteGate : ChapterTasteGate RiemannStieltjesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannStieltjesFromEventFlow (riemannStieltjesToEventFlow x) = some x
    exact RiemannStieltjesUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannStieltjesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance riemannStieltjesFieldFaithful : FieldFaithful RiemannStieltjesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannStieltjesFields
  field_faithful := RiemannStieltjesUpTasteGate_single_carrier_alignment_fields

instance riemannStieltjesNontrivial : Nontrivial RiemannStieltjesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannStieltjesUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RiemannStieltjesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RiemannStieltjesUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RiemannStieltjesUp) ∧ Nonempty (FieldFaithful RiemannStieltjesUp) ∧ Nonempty (BEDC.Meta.TasteGate.Nontrivial RiemannStieltjesUp) ∧ (∀ h : BHist, riemannStieltjesDecodeBHist (riemannStieltjesEncodeBHist h) = h) ∧ (∀ x : RiemannStieltjesUp, riemannStieltjesFromEventFlow (riemannStieltjesToEventFlow x) = some x) ∧ (∀ x y : RiemannStieltjesUp, riemannStieltjesToEventFlow x = riemannStieltjesToEventFlow y → x = y) ∧ riemannStieltjesEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨riemannStieltjesChapterTasteGate⟩,
      ⟨riemannStieltjesFieldFaithful⟩,
      ⟨riemannStieltjesNontrivial⟩,
      RiemannStieltjesUpTasteGate_single_carrier_alignment_decode,
      RiemannStieltjesUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RiemannStieltjesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannStieltjesUp
