import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SturmRootCountUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SturmRootCountUp : Type where
  | mk (P S E V D I A H C K N : BHist) : SturmRootCountUp
  deriving DecidableEq

def sturmRootCountEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sturmRootCountEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sturmRootCountEncodeBHist h

def sturmRootCountDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sturmRootCountDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sturmRootCountDecodeBHist tail)

private theorem SturmRootCountTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, sturmRootCountDecodeBHist (sturmRootCountEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sturmRootCountFields : SturmRootCountUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SturmRootCountUp.mk P S E V D I A H C K N => [P, S, E, V, D, I, A, H, C, K, N]

def sturmRootCountToEventFlow : SturmRootCountUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sturmRootCountFields x).map sturmRootCountEncodeBHist

private def sturmRootCountEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sturmRootCountEventAt index rest

def sturmRootCountFromEventFlow (ef : EventFlow) : Option SturmRootCountUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SturmRootCountUp.mk
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 0 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 1 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 2 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 3 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 4 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 5 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 6 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 7 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 8 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 9 ef))
      (sturmRootCountDecodeBHist (sturmRootCountEventAt 10 ef)))

private theorem SturmRootCountTasteGate_single_carrier_alignment_round_trip
    (x : SturmRootCountUp) :
    sturmRootCountFromEventFlow (sturmRootCountToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P S E V D I A H C K N =>
      change
        some
          (SturmRootCountUp.mk
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist P))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist S))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist E))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist V))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist D))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist I))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist A))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist H))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist C))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist K))
            (sturmRootCountDecodeBHist (sturmRootCountEncodeBHist N))) =
          some (SturmRootCountUp.mk P S E V D I A H C K N)
      rw [SturmRootCountTasteGate_single_carrier_alignment_decode_encode P,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode S,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode E,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode V,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode D,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode I,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode A,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode H,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode C,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode K,
        SturmRootCountTasteGate_single_carrier_alignment_decode_encode N]

private theorem SturmRootCountTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SturmRootCountUp} :
    sturmRootCountToEventFlow x = sturmRootCountToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sturmRootCountFromEventFlow (sturmRootCountToEventFlow x) =
        sturmRootCountFromEventFlow (sturmRootCountToEventFlow y) :=
    congrArg sturmRootCountFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SturmRootCountTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SturmRootCountTasteGate_single_carrier_alignment_round_trip y)))

private theorem SturmRootCountTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SturmRootCountUp, sturmRootCountFields x = sturmRootCountFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P₁ S₁ E₁ V₁ D₁ I₁ A₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk P₂ S₂ E₂ V₂ D₂ I₂ A₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance sturmRootCountBHistCarrier : BHistCarrier SturmRootCountUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sturmRootCountToEventFlow
  fromEventFlow := sturmRootCountFromEventFlow

instance sturmRootCountChapterTasteGate : ChapterTasteGate SturmRootCountUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sturmRootCountFromEventFlow (sturmRootCountToEventFlow x) = some x
    exact SturmRootCountTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SturmRootCountTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sturmRootCountFieldFaithful : FieldFaithful SturmRootCountUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sturmRootCountFields
  field_faithful := SturmRootCountTasteGate_single_carrier_alignment_fields_faithful

instance sturmRootCountNontrivial : Nontrivial SturmRootCountUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SturmRootCountUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SturmRootCountUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def SturmRootCountTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SturmRootCountUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sturmRootCountChapterTasteGate

theorem SturmRootCountTasteGate_single_carrier_alignment :
    (∀ h : BHist, sturmRootCountDecodeBHist (sturmRootCountEncodeBHist h) = h) ∧
      (∀ x : SturmRootCountUp,
        sturmRootCountFromEventFlow (sturmRootCountToEventFlow x) = some x) ∧
        (∀ x y : SturmRootCountUp,
          sturmRootCountToEventFlow x = sturmRootCountToEventFlow y → x = y) ∧
          sturmRootCountEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨SturmRootCountTasteGate_single_carrier_alignment_decode_encode,
      SturmRootCountTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SturmRootCountTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SturmRootCountUp.TasteGate
