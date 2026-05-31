import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxPropertyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxPropertyUp : Type where
  | mk (I F A B Y S M R Q E H C P N : BHist) : DarbouxPropertyUp
  deriving DecidableEq

def darbouxPropertyEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxPropertyEncodeBHist h

def darbouxPropertyDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxPropertyDecodeBHist tail)

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxPropertyFields : DarbouxPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxPropertyUp.mk I F A B Y S M R Q E H C P N =>
      [I, F, A, B, Y, S, M, R, Q, E, H, C, P, N]

def darbouxPropertyToEventFlow : DarbouxPropertyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (darbouxPropertyFields x).map darbouxPropertyEncodeBHist

private def darbouxPropertyEventAt : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxPropertyEventAt index rest

def darbouxPropertyFromEventFlow (ef : EventFlow) : Option DarbouxPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxPropertyUp.mk
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 0 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 1 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 2 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 3 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 4 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 5 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 6 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 7 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 8 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 9 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 10 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 11 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 12 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAt 13 ef)))

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_round_trip
    (x : DarbouxPropertyUp) :
    darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F A B Y S M R Q E H C P N =>
      change
        some
          (DarbouxPropertyUp.mk
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist I))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist F))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist A))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist B))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist Y))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist S))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist M))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist R))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist Q))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist E))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist H))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist C))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist P))
            (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist N))) =
          some (DarbouxPropertyUp.mk I F A B Y S M R Q E H C P N)
      rw [DarbouxPropertyTasteGate_single_carrier_alignment_decode I,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode F,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode A,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode B,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode Y,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode S,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode M,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode R,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode Q,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode E,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode H,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode C,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode P,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode N]

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_injective
    {x y : DarbouxPropertyUp} :
    darbouxPropertyToEventFlow x = darbouxPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) =
        darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow y) :=
    congrArg darbouxPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DarbouxPropertyTasteGate_single_carrier_alignment_round_trip y)))

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_fields :
    ∀ x y : DarbouxPropertyUp, darbouxPropertyFields x = darbouxPropertyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ A₁ B₁ Y₁ S₁ M₁ R₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ F₂ A₂ B₂ Y₂ S₂ M₂ R₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance darbouxPropertyBHistCarrier : BHistCarrier DarbouxPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxPropertyToEventFlow
  fromEventFlow := darbouxPropertyFromEventFlow

instance darbouxPropertyChapterTasteGate : ChapterTasteGate DarbouxPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) = some x
    exact DarbouxPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxPropertyTasteGate_single_carrier_alignment_injective heq)

instance darbouxPropertyFieldFaithful : FieldFaithful DarbouxPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := darbouxPropertyFields
  field_faithful := DarbouxPropertyTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate DarbouxPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxPropertyChapterTasteGate

def taste_gate_witness : FieldFaithful DarbouxPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxPropertyFieldFaithful

theorem DarbouxPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist h) = h) ∧
      (∀ x : DarbouxPropertyUp,
        darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) = some x) ∧
        (∀ x y : DarbouxPropertyUp,
          darbouxPropertyToEventFlow x = darbouxPropertyToEventFlow y → x = y) ∧
          darbouxPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact DarbouxPropertyTasteGate_single_carrier_alignment_decode
  constructor
  · exact DarbouxPropertyTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact DarbouxPropertyTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.DarbouxPropertyUp.TasteGate
