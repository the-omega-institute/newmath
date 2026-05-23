import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicGeometricTailUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicGeometricTailUp : Type where
  | mk (q n W D T R E H C P N : BHist) : DyadicGeometricTailUp
  deriving DecidableEq

def dyadicGeometricTailEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicGeometricTailEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicGeometricTailEncodeBHist h

def dyadicGeometricTailDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicGeometricTailDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicGeometricTailDecodeBHist tail)

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicGeometricTailFields : DyadicGeometricTailUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicGeometricTailUp.mk q n W D T R E H C P N => [q, n, W, D, T, R, E, H, C, P, N]

def dyadicGeometricTailToEventFlow : DyadicGeometricTailUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicGeometricTailFields x).map dyadicGeometricTailEncodeBHist

private def dyadicGeometricTailEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicGeometricTailEventAt index rest

def dyadicGeometricTailFromEventFlow (ef : EventFlow) :
    Option DyadicGeometricTailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicGeometricTailUp.mk
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 0 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 1 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 2 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 3 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 4 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 5 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 6 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 7 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 8 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 9 ef))
      (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEventAt 10 ef)))

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip
    (x : DyadicGeometricTailUp) :
    dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk q n W D T R E H C P N =>
      change
        some
          (DyadicGeometricTailUp.mk
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist q))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist n))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist W))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist D))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist T))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist R))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist E))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist H))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist C))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist P))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist N))) =
          some (DyadicGeometricTailUp.mk q n W D T R E H C P N)
      rw [DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode q,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode n,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode W,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode D,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode T,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode R,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode E,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode H,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode C,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode P,
        DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicGeometricTailUp} :
    dyadicGeometricTailToEventFlow x = dyadicGeometricTailToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) =
        dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow y) :=
    congrArg dyadicGeometricTailFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DyadicGeometricTailUp,
      dyadicGeometricTailFields x = dyadicGeometricTailFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q₁ n₁ W₁ D₁ T₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk q₂ n₂ W₂ D₂ T₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicGeometricTailBHistCarrier : BHistCarrier DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicGeometricTailToEventFlow
  fromEventFlow := dyadicGeometricTailFromEventFlow

instance dyadicGeometricTailChapterTasteGate : ChapterTasteGate DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) = some x
    exact DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicGeometricTailFieldFaithful : FieldFaithful DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicGeometricTailFields
  field_faithful := DyadicGeometricTailTasteGate_single_carrier_alignment_field_faithful

instance dyadicGeometricTailNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicGeometricTailUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DyadicGeometricTailUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DyadicGeometricTailTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicGeometricTailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicGeometricTailChapterTasteGate

theorem DyadicGeometricTailTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist h) = h) ∧
      (∀ x : DyadicGeometricTailUp,
        dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) = some x) ∧
      (∀ x y : DyadicGeometricTailUp,
        dyadicGeometricTailToEventFlow x = dyadicGeometricTailToEventFlow y → x = y) ∧
      dyadicGeometricTailEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode,
      DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicGeometricTailUp
