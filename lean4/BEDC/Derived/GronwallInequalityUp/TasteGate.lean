import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GronwallInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GronwallInequalityUp : Type where
  | mk
      (interval lipschitz envelope dyadicMajorant comparison picardFlow rationalReadback
        transport replay provenance nameCert : BHist) :
      GronwallInequalityUp
  deriving DecidableEq

def gronwallInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gronwallInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gronwallInequalityEncodeBHist h

def gronwallInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gronwallInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gronwallInequalityDecodeBHist tail)

private theorem gronwallInequality_decode_encode :
    ∀ h : BHist, gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gronwallInequalityFields : GronwallInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GronwallInequalityUp.mk interval lipschitz envelope dyadicMajorant comparison picardFlow
      rationalReadback transport replay provenance nameCert =>
      [interval, lipschitz, envelope, dyadicMajorant, comparison, picardFlow,
        rationalReadback, transport, replay, provenance, nameCert]

def gronwallInequalityToEventFlow : GronwallInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gronwallInequalityFields x).map gronwallInequalityEncodeBHist

private def gronwallInequalityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => gronwallInequalityEventAt index rest

def gronwallInequalityFromEventFlow : EventFlow → Option GronwallInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (GronwallInequalityUp.mk
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 0 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 1 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 2 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 3 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 4 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 5 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 6 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 7 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 8 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 9 ef))
        (gronwallInequalityDecodeBHist (gronwallInequalityEventAt 10 ef)))

private theorem gronwallInequality_round_trip :
    ∀ x : GronwallInequalityUp,
      gronwallInequalityFromEventFlow (gronwallInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval lipschitz envelope dyadicMajorant comparison picardFlow rationalReadback
      transport replay provenance nameCert =>
      change
        some
          (GronwallInequalityUp.mk
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist interval))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist lipschitz))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist envelope))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist dyadicMajorant))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist comparison))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist picardFlow))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist rationalReadback))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist transport))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist replay))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist provenance))
            (gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist nameCert))) =
          some
            (GronwallInequalityUp.mk interval lipschitz envelope dyadicMajorant comparison
              picardFlow rationalReadback transport replay provenance nameCert)
      rw [gronwallInequality_decode_encode interval,
        gronwallInequality_decode_encode lipschitz,
        gronwallInequality_decode_encode envelope,
        gronwallInequality_decode_encode dyadicMajorant,
        gronwallInequality_decode_encode comparison,
        gronwallInequality_decode_encode picardFlow,
        gronwallInequality_decode_encode rationalReadback,
        gronwallInequality_decode_encode transport,
        gronwallInequality_decode_encode replay,
        gronwallInequality_decode_encode provenance,
        gronwallInequality_decode_encode nameCert]

private theorem gronwallInequalityToEventFlow_injective {x y : GronwallInequalityUp} :
    gronwallInequalityToEventFlow x = gronwallInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gronwallInequalityFromEventFlow (gronwallInequalityToEventFlow x) =
        gronwallInequalityFromEventFlow (gronwallInequalityToEventFlow y) :=
    congrArg gronwallInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (gronwallInequality_round_trip x).symm
      (Eq.trans hread (gronwallInequality_round_trip y)))

private theorem gronwallInequality_field_faithful :
    ∀ x y : GronwallInequalityUp,
      gronwallInequalityFields x = gronwallInequalityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval₁ lipschitz₁ envelope₁ dyadicMajorant₁ comparison₁ picardFlow₁
      rationalReadback₁ transport₁ replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk interval₂ lipschitz₂ envelope₂ dyadicMajorant₂ comparison₂ picardFlow₂
          rationalReadback₂ transport₂ replay₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance gronwallInequalityBHistCarrier : BHistCarrier GronwallInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gronwallInequalityToEventFlow
  fromEventFlow := gronwallInequalityFromEventFlow

instance gronwallInequalityChapterTasteGate : ChapterTasteGate GronwallInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gronwallInequalityFromEventFlow (gronwallInequalityToEventFlow x) = some x
    exact gronwallInequality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gronwallInequalityToEventFlow_injective heq)

instance gronwallInequalityFieldFaithful : FieldFaithful GronwallInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gronwallInequalityFields
  field_faithful := gronwallInequality_field_faithful

instance gronwallInequalityNontrivial : Nontrivial GronwallInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GronwallInequalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GronwallInequalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem GronwallInequalityTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier GronwallInequalityUp) ∧
      Nonempty (ChapterTasteGate GronwallInequalityUp) ∧
        Nonempty (FieldFaithful GronwallInequalityUp) ∧
          (∀ h : BHist,
            gronwallInequalityDecodeBHist (gronwallInequalityEncodeBHist h) = h) ∧
            (∀ x : GronwallInequalityUp,
              gronwallInequalityFromEventFlow (gronwallInequalityToEventFlow x) = some x) ∧
              (∀ x y : GronwallInequalityUp,
                gronwallInequalityToEventFlow x = gronwallInequalityToEventFlow y → x = y) ∧
                gronwallInequalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨gronwallInequalityBHistCarrier⟩
  constructor
  · exact ⟨gronwallInequalityChapterTasteGate⟩
  constructor
  · exact ⟨gronwallInequalityFieldFaithful⟩
  constructor
  · exact gronwallInequality_decode_encode
  constructor
  · exact gronwallInequality_round_trip
  constructor
  · intro x y heq
    exact gronwallInequalityToEventFlow_injective heq
  · rfl

end BEDC.Derived.GronwallInequalityUp
