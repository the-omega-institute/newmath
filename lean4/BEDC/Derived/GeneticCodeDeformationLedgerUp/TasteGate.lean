import BEDC.Derived.GeneticCodeDeformationLedgerUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneticCodeDeformationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def geneticCodeDeformationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: geneticCodeDeformationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: geneticCodeDeformationLedgerEncodeBHist h

def geneticCodeDeformationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (geneticCodeDeformationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (geneticCodeDeformationLedgerDecodeBHist tail)

private theorem GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def geneticCodeDeformationLedgerFields : BEDC.Derived.GeneticCodeDeformationLedgerUp →
    List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.GeneticCodeDeformationLedgerUp.mk
      tableRow stopSet senseSet roleUAA roleUAG roleUGA roleUGG boundary standardShape
        symmetricDifference transport replay provenance name =>
      [tableRow, stopSet, senseSet, roleUAA, roleUAG, roleUGA, roleUGG, boundary,
        standardShape, symmetricDifference, transport, replay, provenance, name]

def geneticCodeDeformationLedgerToEventFlow :
    BEDC.Derived.GeneticCodeDeformationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (geneticCodeDeformationLedgerFields x).map geneticCodeDeformationLedgerEncodeBHist

private def geneticCodeDeformationLedgerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => geneticCodeDeformationLedgerEventAt index rest

def geneticCodeDeformationLedgerFromEventFlow (ef : EventFlow) :
    Option BEDC.Derived.GeneticCodeDeformationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.GeneticCodeDeformationLedgerUp.mk
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 0 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 1 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 2 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 3 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 4 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 5 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 6 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 7 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 8 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 9 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 10 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 11 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 12 ef))
      (geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEventAt 13 ef)))

private theorem GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.GeneticCodeDeformationLedgerUp) :
    geneticCodeDeformationLedgerFromEventFlow (geneticCodeDeformationLedgerToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T S E A U V W L Std Delta H C P N =>
      change
        some
          (BEDC.Derived.GeneticCodeDeformationLedgerUp.mk
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist T))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist S))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist E))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist A))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist U))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist V))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist W))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist L))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist Std))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist Delta))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist H))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist C))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist P))
            (geneticCodeDeformationLedgerDecodeBHist
              (geneticCodeDeformationLedgerEncodeBHist N))) =
          some
            (BEDC.Derived.GeneticCodeDeformationLedgerUp.mk
              T S E A U V W L Std Delta H C P N)
      rw [GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode T,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode S,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode E,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode A,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode U,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode V,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode W,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode L,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode Std,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode Delta,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode H,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode C,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode P,
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode N]

private theorem GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.GeneticCodeDeformationLedgerUp} :
    geneticCodeDeformationLedgerToEventFlow x = geneticCodeDeformationLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      geneticCodeDeformationLedgerFromEventFlow (geneticCodeDeformationLedgerToEventFlow x) =
        geneticCodeDeformationLedgerFromEventFlow
          (geneticCodeDeformationLedgerToEventFlow y) :=
    congrArg geneticCodeDeformationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BEDC.Derived.GeneticCodeDeformationLedgerUp,
      geneticCodeDeformationLedgerFields x = geneticCodeDeformationLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ S₁ E₁ A₁ U₁ V₁ W₁ L₁ Std₁ Delta₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ S₂ E₂ A₂ U₂ V₂ W₂ L₂ Std₂ Delta₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance geneticCodeDeformationLedgerBHistCarrier :
    BHistCarrier BEDC.Derived.GeneticCodeDeformationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := geneticCodeDeformationLedgerToEventFlow
  fromEventFlow := geneticCodeDeformationLedgerFromEventFlow

instance geneticCodeDeformationLedgerChapterTasteGate :
    ChapterTasteGate BEDC.Derived.GeneticCodeDeformationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      geneticCodeDeformationLedgerFromEventFlow
          (geneticCodeDeformationLedgerToEventFlow x) =
        some x
    exact GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance geneticCodeDeformationLedgerFieldFaithful :
    FieldFaithful BEDC.Derived.GeneticCodeDeformationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := geneticCodeDeformationLedgerFields
  field_faithful :=
    GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_field_faithful

instance geneticCodeDeformationLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BEDC.Derived.GeneticCodeDeformationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.GeneticCodeDeformationLedgerUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BEDC.Derived.GeneticCodeDeformationLedgerUp.mk
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.GeneticCodeDeformationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  geneticCodeDeformationLedgerChapterTasteGate

theorem GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      geneticCodeDeformationLedgerDecodeBHist (geneticCodeDeformationLedgerEncodeBHist h) =
        h) ∧
      (∀ x : BEDC.Derived.GeneticCodeDeformationLedgerUp,
        geneticCodeDeformationLedgerFromEventFlow
            (geneticCodeDeformationLedgerToEventFlow x) =
          some x) ∧
      (∀ x y : BEDC.Derived.GeneticCodeDeformationLedgerUp,
        geneticCodeDeformationLedgerToEventFlow x =
          geneticCodeDeformationLedgerToEventFlow y → x = y) ∧
      geneticCodeDeformationLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_decode,
      GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        GeneticCodeDeformationLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.GeneticCodeDeformationLedgerUp
