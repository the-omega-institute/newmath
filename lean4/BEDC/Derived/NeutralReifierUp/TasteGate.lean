import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NeutralReifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NeutralReifierUp : Type where
  | mk (T Z V U R A H C P N : BHist) : NeutralReifierUp
  deriving DecidableEq

def neutralReifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: neutralReifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: neutralReifierEncodeBHist h

def neutralReifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (neutralReifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (neutralReifierDecodeBHist tail)

private theorem NeutralReifierTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      neutralReifierDecodeBHist (neutralReifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def neutralReifierFields : NeutralReifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NeutralReifierUp.mk T Z V U R A H C P N => [T, Z, V, U, R, A, H, C, P, N]

def neutralReifierToEventFlow : NeutralReifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (neutralReifierFields x).map neutralReifierEncodeBHist

private def neutralReifierEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => neutralReifierEventAt index rest

def neutralReifierFromEventFlow (ef : EventFlow) : Option NeutralReifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NeutralReifierUp.mk
      (neutralReifierDecodeBHist (neutralReifierEventAt 0 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 1 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 2 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 3 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 4 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 5 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 6 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 7 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 8 ef))
      (neutralReifierDecodeBHist (neutralReifierEventAt 9 ef)))

private theorem NeutralReifierTasteGate_single_carrier_alignment_round_trip
    (x : NeutralReifierUp) :
    neutralReifierFromEventFlow (neutralReifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T Z V U R A H C P N =>
      change
        some
          (NeutralReifierUp.mk
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist T))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist Z))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist V))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist U))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist R))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist A))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist H))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist C))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist P))
            (neutralReifierDecodeBHist (neutralReifierEncodeBHist N))) =
          some (NeutralReifierUp.mk T Z V U R A H C P N)
      rw [NeutralReifierTasteGate_single_carrier_alignment_decode_encode T,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode Z,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode V,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode U,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode R,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode A,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode H,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode C,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode P,
        NeutralReifierTasteGate_single_carrier_alignment_decode_encode N]

private theorem neutralReifierToEventFlow_injective {x y : NeutralReifierUp} :
    neutralReifierToEventFlow x = neutralReifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      neutralReifierFromEventFlow (neutralReifierToEventFlow x) =
        neutralReifierFromEventFlow (neutralReifierToEventFlow y) :=
    congrArg neutralReifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NeutralReifierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NeutralReifierTasteGate_single_carrier_alignment_round_trip y)))

private theorem NeutralReifierTasteGate_single_carrier_alignment_fields :
    ∀ x y : NeutralReifierUp, neutralReifierFields x = neutralReifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ Z₁ V₁ U₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ Z₂ V₂ U₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance neutralReifierBHistCarrier : BHistCarrier NeutralReifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := neutralReifierToEventFlow
  fromEventFlow := neutralReifierFromEventFlow

instance neutralReifierChapterTasteGate : ChapterTasteGate NeutralReifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change neutralReifierFromEventFlow (neutralReifierToEventFlow x) = some x
    exact NeutralReifierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (neutralReifierToEventFlow_injective heq)

instance neutralReifierFieldFaithful : FieldFaithful NeutralReifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := neutralReifierFields
  field_faithful := NeutralReifierTasteGate_single_carrier_alignment_fields

instance neutralReifierNontrivial : BEDC.Meta.TasteGate.Nontrivial NeutralReifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NeutralReifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NeutralReifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem NeutralReifierTasteGate_single_carrier_alignment :
    (∀ h : BHist, neutralReifierDecodeBHist (neutralReifierEncodeBHist h) = h) ∧
      (∀ x : NeutralReifierUp,
        neutralReifierFromEventFlow (neutralReifierToEventFlow x) = some x) ∧
        (∀ x y : NeutralReifierUp,
          neutralReifierToEventFlow x = neutralReifierToEventFlow y → x = y) ∧
          neutralReifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact NeutralReifierTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact NeutralReifierTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact neutralReifierToEventFlow_injective heq
  · rfl

end BEDC.Derived.NeutralReifierUp
