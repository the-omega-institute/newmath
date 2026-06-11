import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompactnessUp : Type where
  | mk (M K B U W S H C P N : BHist) : LocatedCompactnessUp
  deriving DecidableEq

def locatedCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompactnessEncodeBHist h

def locatedCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompactnessDecodeBHist tail)

private theorem LocatedCompactnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompactnessFields : LocatedCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompactnessUp.mk M K B U W S H C P N => [M, K, B, U, W, S, H, C, P, N]

def locatedCompactnessToEventFlow : LocatedCompactnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCompactnessFields x).map locatedCompactnessEncodeBHist

private def locatedCompactnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompactnessEventAtDefault index rest

def locatedCompactnessFromEventFlow (ef : EventFlow) : Option LocatedCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompactnessUp.mk
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 0 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 1 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 2 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 3 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 4 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 5 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 6 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 7 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 8 ef))
      (locatedCompactnessDecodeBHist (locatedCompactnessEventAtDefault 9 ef)))

private theorem LocatedCompactnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompactnessUp,
      locatedCompactnessFromEventFlow (locatedCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K B U W S H C P N =>
      change
        some
          (LocatedCompactnessUp.mk
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist M))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist K))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist B))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist U))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist W))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist S))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist H))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist C))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist P))
            (locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist N))) =
          some (LocatedCompactnessUp.mk M K B U W S H C P N)
      rw [LocatedCompactnessTasteGate_single_carrier_alignment_decode M,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode K,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode B,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode U,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode W,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode S,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode H,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode C,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode P,
        LocatedCompactnessTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompactnessUp} :
    locatedCompactnessToEventFlow x = locatedCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompactnessFromEventFlow (locatedCompactnessToEventFlow x) =
        locatedCompactnessFromEventFlow (locatedCompactnessToEventFlow y) :=
    congrArg locatedCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompactnessTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompactnessBHistCarrier : BHistCarrier LocatedCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompactnessToEventFlow
  fromEventFlow := locatedCompactnessFromEventFlow

instance locatedCompactnessChapterTasteGate : ChapterTasteGate LocatedCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompactnessFromEventFlow (locatedCompactnessToEventFlow x) = some x
    exact LocatedCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedCompactnessFieldFaithful : FieldFaithful LocatedCompactnessUp where
  fields := locatedCompactnessFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk M₁ K₁ B₁ U₁ W₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ K₂ B₂ U₂ W₂ S₂ H₂ C₂ P₂ N₂ =>
        simp only [locatedCompactnessFields] at h
        injection h with hM tailM
        injection tailM with hK tailK
        injection tailK with hB tailB
        injection tailB with hU tailU
        injection tailU with hW tailW
        injection tailW with hS tailS
        injection tailS with hH tailH
        injection tailH with hC tailC
        injection tailC with hP tailP
        injection tailP with hN _
        subst hM
        subst hK
        subst hB
        subst hU
        subst hW
        subst hS
        subst hH
        subst hC
        subst hP
        subst hN
        rfl

instance locatedCompactnessNontrivial : Nontrivial LocatedCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedCompactnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedCompactnessUp) ∧
      Nonempty (FieldFaithful LocatedCompactnessUp) ∧
        Nonempty (Nontrivial LocatedCompactnessUp) ∧
          (∀ h : BHist,
            locatedCompactnessDecodeBHist (locatedCompactnessEncodeBHist h) = h) ∧
            (∀ x : LocatedCompactnessUp,
              locatedCompactnessFromEventFlow (locatedCompactnessToEventFlow x) = some x) ∧
              (∀ x y : LocatedCompactnessUp,
                locatedCompactnessToEventFlow x = locatedCompactnessToEventFlow y → x = y) ∧
                locatedCompactnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨locatedCompactnessChapterTasteGate⟩,
      ⟨locatedCompactnessFieldFaithful⟩,
      ⟨locatedCompactnessNontrivial⟩,
      LocatedCompactnessTasteGate_single_carrier_alignment_decode,
      LocatedCompactnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCompactnessUp
