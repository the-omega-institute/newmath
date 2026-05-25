import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FeketeSubadditiveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FeketeSubadditiveUp : Type where
  | mk
      (source subadditivity average lowerBound regularHandoff realSeal transport replay
        provenance nameCert : BHist) :
      FeketeSubadditiveUp
  deriving DecidableEq

def feketeSubadditiveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: feketeSubadditiveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: feketeSubadditiveEncodeBHist h

def feketeSubadditiveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (feketeSubadditiveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (feketeSubadditiveDecodeBHist tail)

private theorem feketeSubadditive_decode_encode :
    ∀ h : BHist, feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def feketeSubadditiveFields : FeketeSubadditiveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FeketeSubadditiveUp.mk source subadditivity average lowerBound regularHandoff realSeal
      transport replay provenance nameCert =>
      [source, subadditivity, average, lowerBound, regularHandoff, realSeal, transport,
        replay, provenance, nameCert]

def feketeSubadditiveToEventFlow : FeketeSubadditiveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (feketeSubadditiveFields x).map feketeSubadditiveEncodeBHist

private def feketeSubadditiveEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => feketeSubadditiveEventAt index rest

def feketeSubadditiveFromEventFlow : EventFlow → Option FeketeSubadditiveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FeketeSubadditiveUp.mk
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 0 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 1 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 2 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 3 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 4 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 5 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 6 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 7 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 8 ef))
        (feketeSubadditiveDecodeBHist (feketeSubadditiveEventAt 9 ef)))

private theorem feketeSubadditive_round_trip :
    ∀ x : FeketeSubadditiveUp,
      feketeSubadditiveFromEventFlow (feketeSubadditiveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source subadditivity average lowerBound regularHandoff realSeal transport replay
      provenance nameCert =>
      change
        some
          (FeketeSubadditiveUp.mk
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist source))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist subadditivity))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist average))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist lowerBound))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist regularHandoff))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist realSeal))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist transport))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist replay))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist provenance))
            (feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist nameCert))) =
          some
            (FeketeSubadditiveUp.mk source subadditivity average lowerBound regularHandoff
              realSeal transport replay provenance nameCert)
      rw [feketeSubadditive_decode_encode source,
        feketeSubadditive_decode_encode subadditivity,
        feketeSubadditive_decode_encode average,
        feketeSubadditive_decode_encode lowerBound,
        feketeSubadditive_decode_encode regularHandoff,
        feketeSubadditive_decode_encode realSeal,
        feketeSubadditive_decode_encode transport,
        feketeSubadditive_decode_encode replay,
        feketeSubadditive_decode_encode provenance,
        feketeSubadditive_decode_encode nameCert]

private theorem feketeSubadditiveToEventFlow_injective {x y : FeketeSubadditiveUp} :
    feketeSubadditiveToEventFlow x = feketeSubadditiveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      feketeSubadditiveFromEventFlow (feketeSubadditiveToEventFlow x) =
        feketeSubadditiveFromEventFlow (feketeSubadditiveToEventFlow y) :=
    congrArg feketeSubadditiveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (feketeSubadditive_round_trip x).symm
      (Eq.trans hread (feketeSubadditive_round_trip y)))

private theorem feketeSubadditive_field_faithful :
    ∀ x y : FeketeSubadditiveUp,
      feketeSubadditiveFields x = feketeSubadditiveFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ subadditivity₁ average₁ lowerBound₁ regularHandoff₁ realSeal₁ transport₁
      replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk source₂ subadditivity₂ average₂ lowerBound₂ regularHandoff₂ realSeal₂ transport₂
          replay₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance feketeSubadditiveBHistCarrier : BHistCarrier FeketeSubadditiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := feketeSubadditiveToEventFlow
  fromEventFlow := feketeSubadditiveFromEventFlow

instance feketeSubadditiveChapterTasteGate : ChapterTasteGate FeketeSubadditiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change feketeSubadditiveFromEventFlow (feketeSubadditiveToEventFlow x) = some x
    exact feketeSubadditive_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (feketeSubadditiveToEventFlow_injective heq)

instance feketeSubadditiveFieldFaithful : FieldFaithful FeketeSubadditiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := feketeSubadditiveFields
  field_faithful := feketeSubadditive_field_faithful

instance feketeSubadditiveNontrivial : Nontrivial FeketeSubadditiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FeketeSubadditiveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FeketeSubadditiveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FeketeSubadditiveTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FeketeSubadditiveUp) ∧
      Nonempty (ChapterTasteGate FeketeSubadditiveUp) ∧
        Nonempty (FieldFaithful FeketeSubadditiveUp) ∧
          (∀ h : BHist,
            feketeSubadditiveDecodeBHist (feketeSubadditiveEncodeBHist h) = h) ∧
            (∀ x : FeketeSubadditiveUp,
              feketeSubadditiveFromEventFlow (feketeSubadditiveToEventFlow x) = some x) ∧
              (∀ x y : FeketeSubadditiveUp,
                feketeSubadditiveToEventFlow x = feketeSubadditiveToEventFlow y → x = y) ∧
                feketeSubadditiveEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨feketeSubadditiveBHistCarrier⟩
  constructor
  · exact ⟨feketeSubadditiveChapterTasteGate⟩
  constructor
  · exact ⟨feketeSubadditiveFieldFaithful⟩
  constructor
  · exact feketeSubadditive_decode_encode
  constructor
  · exact feketeSubadditive_round_trip
  constructor
  · intro x y heq
    exact feketeSubadditiveToEventFlow_injective heq
  · rfl

end BEDC.Derived.FeketeSubadditiveUp
