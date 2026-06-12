import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HolderSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HolderSpaceUp : Type where
  | mk (X d F a K U H C P N : BHist) : HolderSpaceUp
  deriving DecidableEq

def holderSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: holderSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: holderSpaceEncodeBHist h

def holderSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (holderSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (holderSpaceDecodeBHist tail)

private theorem HolderSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, holderSpaceDecodeBHist (holderSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def holderSpaceFields : HolderSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HolderSpaceUp.mk X d F a K U H C P N => [X, d, F, a, K, U, H, C, P, N]

def holderSpaceToEventFlow : HolderSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (holderSpaceFields x).map holderSpaceEncodeBHist

private def holderSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => holderSpaceEventAtDefault index rest

def holderSpaceFromEventFlow (ef : EventFlow) : Option HolderSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HolderSpaceUp.mk
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 0 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 1 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 2 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 3 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 4 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 5 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 6 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 7 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 8 ef))
      (holderSpaceDecodeBHist (holderSpaceEventAtDefault 9 ef)))

private theorem HolderSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HolderSpaceUp, holderSpaceFromEventFlow (holderSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d F a K U H C P N =>
      change
        some
          (HolderSpaceUp.mk
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist X))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist d))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist F))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist a))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist K))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist U))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist H))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist C))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist P))
            (holderSpaceDecodeBHist (holderSpaceEncodeBHist N))) =
          some (HolderSpaceUp.mk X d F a K U H C P N)
      rw [HolderSpaceTasteGate_single_carrier_alignment_decode X,
        HolderSpaceTasteGate_single_carrier_alignment_decode d,
        HolderSpaceTasteGate_single_carrier_alignment_decode F,
        HolderSpaceTasteGate_single_carrier_alignment_decode a,
        HolderSpaceTasteGate_single_carrier_alignment_decode K,
        HolderSpaceTasteGate_single_carrier_alignment_decode U,
        HolderSpaceTasteGate_single_carrier_alignment_decode H,
        HolderSpaceTasteGate_single_carrier_alignment_decode C,
        HolderSpaceTasteGate_single_carrier_alignment_decode P,
        HolderSpaceTasteGate_single_carrier_alignment_decode N]

private theorem HolderSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HolderSpaceUp} :
    holderSpaceToEventFlow x = holderSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      holderSpaceFromEventFlow (holderSpaceToEventFlow x) =
        holderSpaceFromEventFlow (holderSpaceToEventFlow y) :=
    congrArg holderSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HolderSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HolderSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance holderSpaceBHistCarrier : BHistCarrier HolderSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := holderSpaceToEventFlow
  fromEventFlow := holderSpaceFromEventFlow

instance holderSpaceChapterTasteGate : ChapterTasteGate HolderSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change holderSpaceFromEventFlow (holderSpaceToEventFlow x) = some x
    exact HolderSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HolderSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

private theorem HolderSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : HolderSpaceUp, holderSpaceFields x = holderSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 d1 F1 a1 K1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 d2 F2 a2 K2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance holderSpaceFieldFaithful : FieldFaithful HolderSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := holderSpaceFields
  field_faithful := HolderSpaceTasteGate_single_carrier_alignment_fields

instance holderSpaceNontrivial : BEDC.Meta.TasteGate.Nontrivial HolderSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HolderSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HolderSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HolderSpaceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier HolderSpaceUp) ∧
      Nonempty (ChapterTasteGate HolderSpaceUp) ∧
        Nonempty (FieldFaithful HolderSpaceUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial HolderSpaceUp) ∧
            holderSpaceFields
                (HolderSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨holderSpaceBHistCarrier⟩,
      ⟨holderSpaceChapterTasteGate⟩,
      ⟨holderSpaceFieldFaithful⟩,
      ⟨holderSpaceNontrivial⟩,
      rfl⟩

end BEDC.Derived.HolderSpaceUp
