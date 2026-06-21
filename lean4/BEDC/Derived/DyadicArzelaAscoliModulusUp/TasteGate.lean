import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicArzelaAscoliModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicArzelaAscoliModulusUp : Type where
  | mk (K F D S R E M H C P N : BHist) : DyadicArzelaAscoliModulusUp
  deriving DecidableEq

def dyadicArzelaAscoliModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicArzelaAscoliModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicArzelaAscoliModulusEncodeBHist h

def dyadicArzelaAscoliModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicArzelaAscoliModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicArzelaAscoliModulusDecodeBHist tail)

private theorem DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicArzelaAscoliModulusFields :
    DyadicArzelaAscoliModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicArzelaAscoliModulusUp.mk K F D S R E M H C P N =>
      [K, F, D, S, R, E, M, H, C, P, N]

def dyadicArzelaAscoliModulusToEventFlow :
    DyadicArzelaAscoliModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (dyadicArzelaAscoliModulusFields x).map dyadicArzelaAscoliModulusEncodeBHist

private def dyadicArzelaAscoliModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dyadicArzelaAscoliModulusEventAtDefault index rest

def dyadicArzelaAscoliModulusFromEventFlow
    (ef : EventFlow) : Option DyadicArzelaAscoliModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicArzelaAscoliModulusUp.mk
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 0 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 1 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 2 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 3 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 4 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 5 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 6 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 7 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 8 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 9 ef))
      (dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEventAtDefault 10 ef)))

private theorem DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicArzelaAscoliModulusUp,
      dyadicArzelaAscoliModulusFromEventFlow
        (dyadicArzelaAscoliModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K F D S R E M H C P N =>
      change
        some
          (DyadicArzelaAscoliModulusUp.mk
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist K))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist F))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist D))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist S))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist R))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist E))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist M))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist H))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist C))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist P))
            (dyadicArzelaAscoliModulusDecodeBHist
              (dyadicArzelaAscoliModulusEncodeBHist N))) =
          some (DyadicArzelaAscoliModulusUp.mk K F D S R E M H C P N)
      rw [DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode K,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode F,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode D,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode S,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode R,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode E,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode M,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode H,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode C,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode P,
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode N]

private theorem DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicArzelaAscoliModulusUp} :
    dyadicArzelaAscoliModulusToEventFlow x =
      dyadicArzelaAscoliModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicArzelaAscoliModulusFromEventFlow
          (dyadicArzelaAscoliModulusToEventFlow x) =
        dyadicArzelaAscoliModulusFromEventFlow
          (dyadicArzelaAscoliModulusToEventFlow y) :=
    congrArg dyadicArzelaAscoliModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicArzelaAscoliModulusUp,
      dyadicArzelaAscoliModulusFields x =
        dyadicArzelaAscoliModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ D₁ S₁ R₁ E₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ D₂ S₂ R₂ E₂ M₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicArzelaAscoliModulusBHistCarrier :
    BHistCarrier DyadicArzelaAscoliModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicArzelaAscoliModulusToEventFlow
  fromEventFlow := dyadicArzelaAscoliModulusFromEventFlow

instance dyadicArzelaAscoliModulusChapterTasteGate :
    ChapterTasteGate DyadicArzelaAscoliModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicArzelaAscoliModulusFromEventFlow
        (dyadicArzelaAscoliModulusToEventFlow x) = some x
    exact DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicArzelaAscoliModulusFieldFaithful :
    FieldFaithful DyadicArzelaAscoliModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicArzelaAscoliModulusFields
  field_faithful := DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_fields

instance dyadicArzelaAscoliModulusNontrivial :
    Nontrivial DyadicArzelaAscoliModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicArzelaAscoliModulusUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DyadicArzelaAscoliModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicArzelaAscoliModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicArzelaAscoliModulusChapterTasteGate

theorem DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicArzelaAscoliModulusDecodeBHist
        (dyadicArzelaAscoliModulusEncodeBHist h) = h) ∧
      (∀ x : DyadicArzelaAscoliModulusUp,
        dyadicArzelaAscoliModulusFromEventFlow
          (dyadicArzelaAscoliModulusToEventFlow x) = some x) ∧
        (∀ x y : DyadicArzelaAscoliModulusUp,
          dyadicArzelaAscoliModulusToEventFlow x =
            dyadicArzelaAscoliModulusToEventFlow y -> x = y) ∧
          dyadicArzelaAscoliModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_decode,
      DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicArzelaAscoliModulusTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.DyadicArzelaAscoliModulusUp
