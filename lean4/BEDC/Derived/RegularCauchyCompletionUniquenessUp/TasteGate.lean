import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionUniquenessUp : Type where
  | mk (L R D S Q E T H C P N : BHist) : RegularCauchyCompletionUniquenessUp
  deriving DecidableEq

def regularCauchyCompletionUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionUniquenessEncodeBHist h

def regularCauchyCompletionUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionUniquenessDecodeBHist tail)

private theorem RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompletionUniquenessDecodeBHist
          (regularCauchyCompletionUniquenessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionUniquenessFields :
    RegularCauchyCompletionUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionUniquenessUp.mk L R D S Q E T H C P N =>
      [L, R, D, S, Q, E, T, H, C, P, N]

def regularCauchyCompletionUniquenessToEventFlow :
    RegularCauchyCompletionUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyCompletionUniquenessFields x).map
        regularCauchyCompletionUniquenessEncodeBHist

private def regularCauchyCompletionUniquenessEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCompletionUniquenessEventAt index rest

def regularCauchyCompletionUniquenessFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompletionUniquenessUp.mk
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 0 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 1 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 2 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 3 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 4 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 5 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 6 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 7 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 8 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 9 ef))
      (regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEventAt 10 ef)))

private theorem RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyCompletionUniquenessUp) :
    regularCauchyCompletionUniquenessFromEventFlow
        (regularCauchyCompletionUniquenessToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L R D S Q E T H C P N =>
      change
        some
          (RegularCauchyCompletionUniquenessUp.mk
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist L))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist R))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist D))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist S))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist Q))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist E))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist T))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist H))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist C))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist P))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist N))) =
          some (RegularCauchyCompletionUniquenessUp.mk L R D S Q E T H C P N)
      rw [RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode L,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode R,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode D,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode S,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode E,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode T,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionUniquenessUp} :
    regularCauchyCompletionUniquenessToEventFlow x =
        regularCauchyCompletionUniquenessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) =
        regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow y) :=
    congrArg regularCauchyCompletionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyCompletionUniquenessUp,
      regularCauchyCompletionUniquenessFields x =
          regularCauchyCompletionUniquenessFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ R₁ D₁ S₁ Q₁ E₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ R₂ D₂ S₂ Q₂ E₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyCompletionUniquenessBHistCarrier :
    BHistCarrier RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionUniquenessToEventFlow
  fromEventFlow := regularCauchyCompletionUniquenessFromEventFlow

instance regularCauchyCompletionUniquenessChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) =
        some x
    exact RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyCompletionUniquenessFieldFaithful :
    FieldFaithful RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompletionUniquenessFields
  field_faithful :=
    RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_fields

instance regularCauchyCompletionUniquenessNontrivial :
    Nontrivial RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionUniquenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCompletionUniquenessUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionUniquenessUp,
        regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyCompletionUniquenessUp,
        regularCauchyCompletionUniquenessToEventFlow x =
            regularCauchyCompletionUniquenessToEventFlow y →
          x = y) ∧
      regularCauchyCompletionUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_decode,
      RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyCompletionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionUniquenessUp
