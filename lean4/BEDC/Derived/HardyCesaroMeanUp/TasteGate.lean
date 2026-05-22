import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardyCesaroMeanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardyCesaroMeanUp : Type where
  | mk (S P U D R E T C Q N : BHist) : HardyCesaroMeanUp
  deriving DecidableEq

def hardyCesaroMeanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardyCesaroMeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardyCesaroMeanEncodeBHist h

def hardyCesaroMeanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardyCesaroMeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardyCesaroMeanDecodeBHist tail)

private theorem HardyCesaroMeanTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hardyCesaroMeanToEventFlow : HardyCesaroMeanUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HardyCesaroMeanUp.mk S P U D R E T C Q N =>
      [[BMark.b0],
        hardyCesaroMeanEncodeBHist S,
        [BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hardyCesaroMeanEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hardyCesaroMeanEncodeBHist N]

private def hardyCesaroMeanEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hardyCesaroMeanEventAtDefault index rest

def hardyCesaroMeanFromEventFlow (ef : EventFlow) : Option HardyCesaroMeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HardyCesaroMeanUp.mk
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 1 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 3 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 5 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 7 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 9 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 11 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 13 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 15 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 17 ef))
      (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEventAtDefault 19 ef)))

private theorem HardyCesaroMeanTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HardyCesaroMeanUp,
      hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S P U D R E T C Q N =>
      change
        some
          (HardyCesaroMeanUp.mk
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist S))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist P))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist U))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist D))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist R))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist E))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist T))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist C))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist Q))
            (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist N))) =
          some (HardyCesaroMeanUp.mk S P U D R E T C Q N)
      rw [HardyCesaroMeanTasteGate_single_carrier_alignment_decode S,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode P,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode U,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode D,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode R,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode E,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode T,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode C,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode Q,
        HardyCesaroMeanTasteGate_single_carrier_alignment_decode N]

private theorem HardyCesaroMeanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HardyCesaroMeanUp} :
    hardyCesaroMeanToEventFlow x = hardyCesaroMeanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) =
        hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow y) :=
    congrArg hardyCesaroMeanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HardyCesaroMeanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HardyCesaroMeanTasteGate_single_carrier_alignment_round_trip y)))

private def hardyCesaroMeanFields : HardyCesaroMeanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HardyCesaroMeanUp.mk S P U D R E T C Q N => [S, P, U, D, R, E, T, C, Q, N]

private theorem HardyCesaroMeanTasteGate_single_carrier_alignment_fields :
    ∀ x y : HardyCesaroMeanUp, hardyCesaroMeanFields x = hardyCesaroMeanFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 P1 U1 D1 R1 E1 T1 C1 Q1 N1 =>
      cases y with
      | mk S2 P2 U2 D2 R2 E2 T2 C2 Q2 N2 =>
          cases hfields
          rfl

instance hardyCesaroMeanBHistCarrier : BHistCarrier HardyCesaroMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardyCesaroMeanToEventFlow
  fromEventFlow := hardyCesaroMeanFromEventFlow

instance hardyCesaroMeanChapterTasteGate : ChapterTasteGate HardyCesaroMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) = some x
    exact HardyCesaroMeanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HardyCesaroMeanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hardyCesaroMeanFieldFaithful : FieldFaithful HardyCesaroMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hardyCesaroMeanFields
  field_faithful := HardyCesaroMeanTasteGate_single_carrier_alignment_fields

instance hardyCesaroMeanNontrivial : Nontrivial HardyCesaroMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HardyCesaroMeanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HardyCesaroMeanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HardyCesaroMeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hardyCesaroMeanChapterTasteGate

theorem HardyCesaroMeanTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HardyCesaroMeanUp) ∧
      Nonempty (FieldFaithful HardyCesaroMeanUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HardyCesaroMeanUp) ∧
          (∀ h : BHist, hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist h) = h) ∧
            (∀ x : HardyCesaroMeanUp,
              hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) = some x) ∧
              (∀ x y : HardyCesaroMeanUp,
                hardyCesaroMeanToEventFlow x = hardyCesaroMeanToEventFlow y → x = y) ∧
                hardyCesaroMeanEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨hardyCesaroMeanChapterTasteGate⟩,
      ⟨hardyCesaroMeanFieldFaithful⟩,
      ⟨hardyCesaroMeanNontrivial⟩,
      HardyCesaroMeanTasteGate_single_carrier_alignment_decode,
      HardyCesaroMeanTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HardyCesaroMeanTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HardyCesaroMeanUp
