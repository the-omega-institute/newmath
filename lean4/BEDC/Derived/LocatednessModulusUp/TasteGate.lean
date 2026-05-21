import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatednessModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatednessModulusUp : Type where
  | mk (q L I D S R E H C P N : BHist) : LocatednessModulusUp
  deriving DecidableEq

def locatednessModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatednessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatednessModulusEncodeBHist h

def locatednessModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatednessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatednessModulusDecodeBHist tail)

private theorem locatednessModulus_decode_encode_bhist :
    ∀ h : BHist, locatednessModulusDecodeBHist (locatednessModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatednessModulusFields : LocatednessModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatednessModulusUp.mk q L I D S R E H C P N => [q, L, I, D, S, R, E, H, C, P, N]

def locatednessModulusToEventFlow : LocatednessModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatednessModulusFields x).map locatednessModulusEncodeBHist

private def locatednessModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatednessModulusEventAt index rest

def locatednessModulusFromEventFlow : EventFlow → Option LocatednessModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatednessModulusUp.mk
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 0 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 1 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 2 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 3 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 4 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 5 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 6 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 7 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 8 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 9 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 10 ef)))

private theorem locatednessModulus_round_trip :
    ∀ x : LocatednessModulusUp,
      locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q L I D S R E H C P N =>
      change
        some
          (LocatednessModulusUp.mk
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist q))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist L))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist I))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist D))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist S))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist R))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist E))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist H))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist C))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist P))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist N))) =
          some (LocatednessModulusUp.mk q L I D S R E H C P N)
      rw [locatednessModulus_decode_encode_bhist q, locatednessModulus_decode_encode_bhist L,
        locatednessModulus_decode_encode_bhist I, locatednessModulus_decode_encode_bhist D,
        locatednessModulus_decode_encode_bhist S, locatednessModulus_decode_encode_bhist R,
        locatednessModulus_decode_encode_bhist E, locatednessModulus_decode_encode_bhist H,
        locatednessModulus_decode_encode_bhist C, locatednessModulus_decode_encode_bhist P,
        locatednessModulus_decode_encode_bhist N]

private theorem locatednessModulusToEventFlow_injective {x y : LocatednessModulusUp} :
    locatednessModulusToEventFlow x = locatednessModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) =
        locatednessModulusFromEventFlow (locatednessModulusToEventFlow y) :=
    congrArg locatednessModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatednessModulus_round_trip x).symm
      (Eq.trans hread (locatednessModulus_round_trip y)))

theorem locatednessModulus_field_faithful :
    ∀ x y : LocatednessModulusUp,
      locatednessModulusFields x = locatednessModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q₁ L₁ I₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk q₂ L₂ I₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatednessModulusBHistCarrier : BHistCarrier LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatednessModulusToEventFlow
  fromEventFlow := locatednessModulusFromEventFlow

instance locatednessModulusChapterTasteGate : ChapterTasteGate LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) = some x
    exact locatednessModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatednessModulusToEventFlow_injective heq)

instance locatednessModulusFieldFaithful : FieldFaithful LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatednessModulusFields
  field_faithful := locatednessModulus_field_faithful

instance locatednessModulusNontrivial : Nontrivial LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatednessModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatednessModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatednessModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatednessModulusChapterTasteGate

theorem LocatednessModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatednessModulusUp) ∧
      Nonempty (FieldFaithful LocatednessModulusUp) ∧
        Nonempty (Nontrivial LocatednessModulusUp) ∧
          (∀ h : BHist, locatednessModulusDecodeBHist (locatednessModulusEncodeBHist h) = h) ∧
            (∀ x : LocatednessModulusUp,
              locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) = some x) ∧
              (∀ x y : LocatednessModulusUp,
                locatednessModulusToEventFlow x = locatednessModulusToEventFlow y → x = y) ∧
                locatednessModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨locatednessModulusChapterTasteGate⟩, ⟨locatednessModulusFieldFaithful⟩,
      ⟨locatednessModulusNontrivial⟩, locatednessModulus_decode_encode_bhist,
      locatednessModulus_round_trip,
      (fun _ _ heq => locatednessModulusToEventFlow_injective heq), rfl⟩

end BEDC.Derived.LocatednessModulusUp.TasteGate

namespace BEDC.Derived.LocatednessModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem LocatednessModulusTasteGate_single_carrier_alignment :
    (TasteGate.locatednessModulusDecodeBHist [BMark.b1] = BHist.e1 BHist.Empty) ∧
      (∀ h : BHist,
        TasteGate.locatednessModulusDecodeBHist
            (TasteGate.locatednessModulusEncodeBHist h) =
          h) ∧
        (∀ x : TasteGate.LocatednessModulusUp,
          TasteGate.locatednessModulusFromEventFlow
              (TasteGate.locatednessModulusToEventFlow x) =
            some x) ∧
          (∀ x y : TasteGate.LocatednessModulusUp,
            TasteGate.locatednessModulusFields x =
                TasteGate.locatednessModulusFields y →
              x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl, TasteGate.LocatednessModulusTasteGate_single_carrier_alignment.2.2.2.1,
      TasteGate.LocatednessModulusTasteGate_single_carrier_alignment.2.2.2.2.1,
      TasteGate.locatednessModulus_field_faithful⟩

end BEDC.Derived.LocatednessModulusUp
