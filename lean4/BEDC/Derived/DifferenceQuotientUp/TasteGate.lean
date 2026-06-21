import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DifferenceQuotientUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DifferenceQuotientUp : Type where
  | mk (X Y A B S D R E H C P N : BHist) : DifferenceQuotientUp
  deriving DecidableEq

instance differenceQuotientInhabited : Inhabited DifferenceQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  default :=
    DifferenceQuotientUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

def differenceQuotientEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: differenceQuotientEncodeBHist h
  | BHist.e1 h => BMark.b1 :: differenceQuotientEncodeBHist h

def differenceQuotientDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (differenceQuotientDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (differenceQuotientDecodeBHist tail)

private theorem DifferenceQuotientTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, differenceQuotientDecodeBHist (differenceQuotientEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def differenceQuotientFields : DifferenceQuotientUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DifferenceQuotientUp.mk X Y A B S D R E H C P N => [X, Y, A, B, S, D, R, E, H, C, P, N]

def differenceQuotientToEventFlow : DifferenceQuotientUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (differenceQuotientFields x).map differenceQuotientEncodeBHist

private def differenceQuotientEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => differenceQuotientEventAtDefault index rest

def differenceQuotientFromEventFlow (ef : EventFlow) : Option DifferenceQuotientUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DifferenceQuotientUp.mk
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 0 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 1 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 2 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 3 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 4 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 5 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 6 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 7 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 8 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 9 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 10 ef))
      (differenceQuotientDecodeBHist (differenceQuotientEventAtDefault 11 ef)))

private theorem DifferenceQuotientTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DifferenceQuotientUp,
      differenceQuotientFromEventFlow (differenceQuotientToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y A B S D R E H C P N =>
      change
        some
          (DifferenceQuotientUp.mk
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist X))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist Y))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist A))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist B))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist S))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist D))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist R))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist E))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist H))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist C))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist P))
            (differenceQuotientDecodeBHist (differenceQuotientEncodeBHist N))) =
          some (DifferenceQuotientUp.mk X Y A B S D R E H C P N)
      rw [DifferenceQuotientTasteGate_single_carrier_alignment_decode X,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode Y,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode A,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode B,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode S,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode D,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode R,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode E,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode H,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode C,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode P,
        DifferenceQuotientTasteGate_single_carrier_alignment_decode N]

private theorem DifferenceQuotientToEventFlow_injective {x y : DifferenceQuotientUp} :
    differenceQuotientToEventFlow x = differenceQuotientToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      differenceQuotientFromEventFlow (differenceQuotientToEventFlow x) =
        differenceQuotientFromEventFlow (differenceQuotientToEventFlow y) :=
    congrArg differenceQuotientFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DifferenceQuotientTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DifferenceQuotientTasteGate_single_carrier_alignment_round_trip y)))

private theorem DifferenceQuotientTasteGate_single_carrier_alignment_fields :
    ∀ x y : DifferenceQuotientUp,
      differenceQuotientFields x = differenceQuotientFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 A1 B1 S1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 A2 B2 S2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance differenceQuotientBHistCarrier : BHistCarrier DifferenceQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := differenceQuotientToEventFlow
  fromEventFlow := differenceQuotientFromEventFlow

instance differenceQuotientChapterTasteGate : ChapterTasteGate DifferenceQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change differenceQuotientFromEventFlow (differenceQuotientToEventFlow x) = some x
    exact DifferenceQuotientTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DifferenceQuotientToEventFlow_injective heq)

instance differenceQuotientFieldFaithful : FieldFaithful DifferenceQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := differenceQuotientFields
  field_faithful := DifferenceQuotientTasteGate_single_carrier_alignment_fields

theorem DifferenceQuotientTasteGate_single_carrier_alignment :
    (∀ h : BHist, differenceQuotientDecodeBHist (differenceQuotientEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DifferenceQuotientUp) ∧
        Nonempty (ChapterTasteGate DifferenceQuotientUp) ∧
          FieldFaithful.field_count DifferenceQuotientUp = 12 ∧
            differenceQuotientToEventFlow
                (DifferenceQuotientUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty) ≠
              differenceQuotientToEventFlow
                (DifferenceQuotientUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨DifferenceQuotientTasteGate_single_carrier_alignment_decode,
      ⟨differenceQuotientBHistCarrier⟩,
      ⟨differenceQuotientChapterTasteGate⟩,
      rfl,
      by
        intro h
        injection h with hhead _tail
        cases hhead⟩

end BEDC.Derived.DifferenceQuotientUp
