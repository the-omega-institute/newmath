import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BedcPhilosophyPackageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BedcPhilosophyPackageUp : Type where
  | mk : (T R M G D S C A H K N : BHist) → BedcPhilosophyPackageUp
  deriving DecidableEq

def bedcPhilosophyPackageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bedcPhilosophyPackageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bedcPhilosophyPackageEncodeBHist h

def bedcPhilosophyPackageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bedcPhilosophyPackageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bedcPhilosophyPackageDecodeBHist tail)

private theorem BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bedcPhilosophyPackageFields : BedcPhilosophyPackageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BedcPhilosophyPackageUp.mk T R M G D S C A H K N => [T, R, M, G, D, S, C, A, H, K, N]

def bedcPhilosophyPackageToEventFlow : BedcPhilosophyPackageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BedcPhilosophyPackageUp.mk T R M G D S C A H K N =>
      [[BMark.b0],
        bedcPhilosophyPackageEncodeBHist T,
        [BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bedcPhilosophyPackageEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcPhilosophyPackageEncodeBHist N]

private def bedcPhilosophyPackageEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bedcPhilosophyPackageEventAtDefault index rest

def bedcPhilosophyPackageFromEventFlow
    (ef : EventFlow) : Option BedcPhilosophyPackageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BedcPhilosophyPackageUp.mk
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 1 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 3 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 5 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 7 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 9 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 11 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 13 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 15 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 17 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 19 ef))
      (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEventAtDefault 21 ef)))

private theorem BedcPhilosophyPackageTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BedcPhilosophyPackageUp,
      bedcPhilosophyPackageFromEventFlow (bedcPhilosophyPackageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T R M G D S C A H K N =>
      change
        some
          (BedcPhilosophyPackageUp.mk
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist T))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist R))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist M))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist G))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist D))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist S))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist C))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist A))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist H))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist K))
            (bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist N))) =
          some (BedcPhilosophyPackageUp.mk T R M G D S C A H K N)
      rw [BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode T,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode R,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode M,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode G,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode D,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode S,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode C,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode A,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode H,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode K,
        BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode N]

private theorem BedcPhilosophyPackageTasteGate_single_carrier_alignment_injective
    {x y : BedcPhilosophyPackageUp} :
    bedcPhilosophyPackageToEventFlow x = bedcPhilosophyPackageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bedcPhilosophyPackageFromEventFlow (bedcPhilosophyPackageToEventFlow x) =
        bedcPhilosophyPackageFromEventFlow (bedcPhilosophyPackageToEventFlow y) :=
    congrArg bedcPhilosophyPackageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BedcPhilosophyPackageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BedcPhilosophyPackageTasteGate_single_carrier_alignment_round_trip y)))

private theorem BedcPhilosophyPackageTasteGate_single_carrier_alignment_fields :
    ∀ x y : BedcPhilosophyPackageUp,
      bedcPhilosophyPackageFields x = bedcPhilosophyPackageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ R₁ M₁ G₁ D₁ S₁ C₁ A₁ H₁ K₁ N₁ =>
      cases y with
      | mk T₂ R₂ M₂ G₂ D₂ S₂ C₂ A₂ H₂ K₂ N₂ =>
          cases hfields
          rfl

instance bedcPhilosophyPackageBHistCarrier : BHistCarrier BedcPhilosophyPackageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bedcPhilosophyPackageToEventFlow
  fromEventFlow := bedcPhilosophyPackageFromEventFlow

instance bedcPhilosophyPackageChapterTasteGate :
    ChapterTasteGate BedcPhilosophyPackageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bedcPhilosophyPackageFromEventFlow (bedcPhilosophyPackageToEventFlow x) = some x
    exact BedcPhilosophyPackageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BedcPhilosophyPackageTasteGate_single_carrier_alignment_injective heq)

instance bedcPhilosophyPackageFieldFaithful : FieldFaithful BedcPhilosophyPackageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bedcPhilosophyPackageFields
  field_faithful := BedcPhilosophyPackageTasteGate_single_carrier_alignment_fields

instance bedcPhilosophyPackageNontrivial : Nontrivial BedcPhilosophyPackageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BedcPhilosophyPackageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BedcPhilosophyPackageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BedcPhilosophyPackageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bedcPhilosophyPackageChapterTasteGate

theorem BedcPhilosophyPackageTasteGate_single_carrier_alignment :
    (∀ h : BHist, bedcPhilosophyPackageDecodeBHist (bedcPhilosophyPackageEncodeBHist h) = h) ∧
      (∀ x : BedcPhilosophyPackageUp,
        bedcPhilosophyPackageFromEventFlow (bedcPhilosophyPackageToEventFlow x) = some x) ∧
        (∀ x y : BedcPhilosophyPackageUp,
          bedcPhilosophyPackageToEventFlow x = bedcPhilosophyPackageToEventFlow y → x = y) ∧
          bedcPhilosophyPackageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BedcPhilosophyPackageTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BedcPhilosophyPackageTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BedcPhilosophyPackageTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.BedcPhilosophyPackageUp
