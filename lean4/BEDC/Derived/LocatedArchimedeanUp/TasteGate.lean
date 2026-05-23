import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedArchimedeanUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedArchimedeanUp : Type where
  | mk (L I A D S R E H C P N : BHist) : LocatedArchimedeanUp
  deriving DecidableEq

def locatedArchimedeanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedArchimedeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedArchimedeanEncodeBHist h

def locatedArchimedeanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedArchimedeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedArchimedeanDecodeBHist tail)

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedArchimedeanFields : LocatedArchimedeanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedArchimedeanUp.mk L I A D S R E H C P N => [L, I, A, D, S, R, E, H, C, P, N]

def locatedArchimedeanToEventFlow : LocatedArchimedeanUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedArchimedeanFields x).map locatedArchimedeanEncodeBHist

private def locatedArchimedeanEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedArchimedeanEventAt index rest

def locatedArchimedeanFromEventFlow (ef : EventFlow) : Option LocatedArchimedeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedArchimedeanUp.mk
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 0 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 1 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 2 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 3 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 4 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 5 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 6 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 7 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 8 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 9 ef))
      (locatedArchimedeanDecodeBHist (locatedArchimedeanEventAt 10 ef)))

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip
    (x : LocatedArchimedeanUp) :
    locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L I A D S R E H C P N =>
      change
        some
          (LocatedArchimedeanUp.mk
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist L))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist I))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist A))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist D))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist S))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist R))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist E))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist H))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist C))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist P))
            (locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist N))) =
          some (LocatedArchimedeanUp.mk L I A D S R E H C P N)
      rw [LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode L,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode I,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode A,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode D,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode S,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode R,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode E,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode H,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode C,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode P,
        LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedArchimedeanUp} :
    locatedArchimedeanToEventFlow x = locatedArchimedeanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) =
        locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow y) :=
    congrArg locatedArchimedeanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedArchimedeanTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedArchimedeanUp, locatedArchimedeanFields x = locatedArchimedeanFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ I₁ A₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ I₂ A₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedArchimedeanBHistCarrier : BHistCarrier LocatedArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedArchimedeanToEventFlow
  fromEventFlow := locatedArchimedeanFromEventFlow

instance locatedArchimedeanChapterTasteGate : ChapterTasteGate LocatedArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) = some x
    exact LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedArchimedeanFieldFaithful : FieldFaithful LocatedArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedArchimedeanFields
  field_faithful := LocatedArchimedeanTasteGate_single_carrier_alignment_fields_faithful

instance locatedArchimedeanNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedArchimedeanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedArchimedeanUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedArchimedeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedArchimedeanChapterTasteGate

theorem LocatedArchimedeanTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedArchimedeanUp) ∧
      Nonempty (FieldFaithful LocatedArchimedeanUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedArchimedeanUp) ∧
          (∀ h : BHist, locatedArchimedeanDecodeBHist (locatedArchimedeanEncodeBHist h) = h) ∧
            (∀ x : LocatedArchimedeanUp,
              locatedArchimedeanFromEventFlow (locatedArchimedeanToEventFlow x) = some x) ∧
              (∀ x y : LocatedArchimedeanUp,
                locatedArchimedeanToEventFlow x = locatedArchimedeanToEventFlow y → x = y) ∧
                locatedArchimedeanEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨locatedArchimedeanChapterTasteGate⟩,
      ⟨locatedArchimedeanFieldFaithful⟩,
      ⟨locatedArchimedeanNontrivial⟩,
      LocatedArchimedeanTasteGate_single_carrier_alignment_decode_encode,
      LocatedArchimedeanTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedArchimedeanUp.TasteGate
