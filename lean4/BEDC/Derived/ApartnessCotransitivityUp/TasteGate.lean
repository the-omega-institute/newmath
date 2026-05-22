import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessCotransitivityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessCotransitivityUp : Type where
  | mk (X Y Z L R D H C P N : BHist) : ApartnessCotransitivityUp
  deriving DecidableEq

def apartnessCotransitivityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessCotransitivityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessCotransitivityEncodeBHist h

def apartnessCotransitivityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessCotransitivityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessCotransitivityDecodeBHist tail)

private theorem ApartnessCotransitivityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apartnessCotransitivityFields : ApartnessCotransitivityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessCotransitivityUp.mk X Y Z L R D H C P N =>
      [X, Y, Z, L, R, D, H, C, P, N]

def apartnessCotransitivityToEventFlow : ApartnessCotransitivityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (apartnessCotransitivityFields x).map apartnessCotransitivityEncodeBHist

private def apartnessCotransitivityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => apartnessCotransitivityEventAt index rest

def apartnessCotransitivityFromEventFlow
    (ef : EventFlow) : Option ApartnessCotransitivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ApartnessCotransitivityUp.mk
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 0 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 1 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 2 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 3 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 4 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 5 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 6 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 7 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 8 ef))
      (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEventAt 9 ef)))

private theorem ApartnessCotransitivityTasteGate_single_carrier_alignment_round_trip
    (x : ApartnessCotransitivityUp) :
    apartnessCotransitivityFromEventFlow (apartnessCotransitivityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y Z L R D H C P N =>
      change
        some
          (ApartnessCotransitivityUp.mk
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist X))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist Y))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist Z))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist L))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist R))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist D))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist H))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist C))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist P))
            (apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist N))) =
          some (ApartnessCotransitivityUp.mk X Y Z L R D H C P N)
      rw [ApartnessCotransitivityTasteGate_single_carrier_alignment_decode X,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode Y,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode Z,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode L,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode R,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode D,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode H,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode C,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode P,
        ApartnessCotransitivityTasteGate_single_carrier_alignment_decode N]

private theorem ApartnessCotransitivityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ApartnessCotransitivityUp} :
    apartnessCotransitivityToEventFlow x = apartnessCotransitivityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessCotransitivityFromEventFlow (apartnessCotransitivityToEventFlow x) =
        apartnessCotransitivityFromEventFlow (apartnessCotransitivityToEventFlow y) :=
    congrArg apartnessCotransitivityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ApartnessCotransitivityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ApartnessCotransitivityTasteGate_single_carrier_alignment_round_trip y)))

private theorem ApartnessCotransitivityTasteGate_single_carrier_alignment_fields :
    ∀ x y : ApartnessCotransitivityUp,
      apartnessCotransitivityFields x = apartnessCotransitivityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ Z₁ L₁ R₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ Z₂ L₂ R₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance apartnessCotransitivityBHistCarrier :
    BHistCarrier ApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessCotransitivityToEventFlow
  fromEventFlow := apartnessCotransitivityFromEventFlow

instance apartnessCotransitivityChapterTasteGate :
    ChapterTasteGate ApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      apartnessCotransitivityFromEventFlow (apartnessCotransitivityToEventFlow x) =
        some x
    exact ApartnessCotransitivityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ApartnessCotransitivityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance apartnessCotransitivityFieldFaithful :
    FieldFaithful ApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apartnessCotransitivityFields
  field_faithful := ApartnessCotransitivityTasteGate_single_carrier_alignment_fields

instance apartnessCotransitivityNontrivial :
    Nontrivial ApartnessCotransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApartnessCotransitivityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApartnessCotransitivityUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ApartnessCotransitivityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      apartnessCotransitivityDecodeBHist (apartnessCotransitivityEncodeBHist h) = h) ∧
      (∀ x : ApartnessCotransitivityUp,
        apartnessCotransitivityFromEventFlow (apartnessCotransitivityToEventFlow x) =
          some x) ∧
      (∀ x y : ApartnessCotransitivityUp,
        apartnessCotransitivityToEventFlow x = apartnessCotransitivityToEventFlow y →
          x = y) ∧
      apartnessCotransitivityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ApartnessCotransitivityTasteGate_single_carrier_alignment_decode,
      ApartnessCotransitivityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ApartnessCotransitivityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ApartnessCotransitivityUp
