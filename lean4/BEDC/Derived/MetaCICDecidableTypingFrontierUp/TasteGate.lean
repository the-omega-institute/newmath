import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDecidableTypingFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDecidableTypingFrontierUp : Type where
  | mk
      (inferType checkSame structuralEq boundedNormal refusal transport replay provenance
        localName : BHist) : MetaCICDecidableTypingFrontierUp
  deriving DecidableEq

def metacicDecidableTypingFrontierEncodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        metacicDecidableTypingFrontierEncodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        metacicDecidableTypingFrontierEncodeBHist h

def metacicDecidableTypingFrontierDecodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (metacicDecidableTypingFrontierDecodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (metacicDecidableTypingFrontierDecodeBHist tail)

private theorem metacicDecidableTypingFrontier_decode_encode_bhist :
    ∀ h : BHist,
      metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicDecidableTypingFrontierFields :
    MetaCICDecidableTypingFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDecidableTypingFrontierUp.mk inferType checkSame structuralEq boundedNormal
      refusal transport replay provenance localName =>
      [inferType, checkSame, structuralEq, boundedNormal, refusal, transport, replay,
        provenance, localName]

def metacicDecidableTypingFrontierToEventFlow :
    MetaCICDecidableTypingFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metacicDecidableTypingFrontierFields x).map
        metacicDecidableTypingFrontierEncodeBHist

private def metacicDecidableTypingFrontierEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metacicDecidableTypingFrontierEventAt index rest

def metacicDecidableTypingFrontierFromEventFlow :
    EventFlow → Option MetaCICDecidableTypingFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetaCICDecidableTypingFrontierUp.mk
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 0 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 1 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 2 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 3 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 4 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 5 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 6 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 7 ef))
        (metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEventAt 8 ef)))

private theorem metacicDecidableTypingFrontier_round_trip :
    ∀ x : MetaCICDecidableTypingFrontierUp,
      metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inferType checkSame structuralEq boundedNormal refusal transport replay provenance
      localName =>
      change
        some
          (MetaCICDecidableTypingFrontierUp.mk
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                inferType))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                checkSame))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                structuralEq))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                boundedNormal))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                refusal))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                transport))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                replay))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                provenance))
            (metacicDecidableTypingFrontierDecodeBHist
              (metacicDecidableTypingFrontierEncodeBHist
                localName))) =
          some
            (MetaCICDecidableTypingFrontierUp.mk inferType checkSame structuralEq
              boundedNormal refusal transport replay provenance localName)
      rw [
        metacicDecidableTypingFrontier_decode_encode_bhist
          inferType,
        metacicDecidableTypingFrontier_decode_encode_bhist
          checkSame,
        metacicDecidableTypingFrontier_decode_encode_bhist
          structuralEq,
        metacicDecidableTypingFrontier_decode_encode_bhist
          boundedNormal,
        metacicDecidableTypingFrontier_decode_encode_bhist
          refusal,
        metacicDecidableTypingFrontier_decode_encode_bhist
          transport,
        metacicDecidableTypingFrontier_decode_encode_bhist
          replay,
        metacicDecidableTypingFrontier_decode_encode_bhist
          provenance,
        metacicDecidableTypingFrontier_decode_encode_bhist
          localName]

private theorem
    metacicDecidableTypingFrontierToEventFlow_injective
    {x y : MetaCICDecidableTypingFrontierUp} :
    metacicDecidableTypingFrontierToEventFlow x =
        metacicDecidableTypingFrontierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow x) =
        metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow y) :=
    congrArg metacicDecidableTypingFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (metacicDecidableTypingFrontier_round_trip x).symm
      (Eq.trans hread
        (metacicDecidableTypingFrontier_round_trip y)))

private theorem
    metacicDecidableTypingFrontierFields_faithful :
    ∀ x y : MetaCICDecidableTypingFrontierUp,
      metacicDecidableTypingFrontierFields x =
        metacicDecidableTypingFrontierFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk inferType₁ checkSame₁ structuralEq₁ boundedNormal₁ refusal₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk inferType₂ checkSame₂ structuralEq₂ boundedNormal₂ refusal₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance metacicDecidableTypingFrontierBHistCarrier :
    BHistCarrier MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDecidableTypingFrontierToEventFlow
  fromEventFlow :=
    metacicDecidableTypingFrontierFromEventFlow

instance metacicDecidableTypingFrontierChapterTasteGate :
    ChapterTasteGate MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDecidableTypingFrontierFromEventFlow
          (metacicDecidableTypingFrontierToEventFlow x) =
        some x
    exact metacicDecidableTypingFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (metacicDecidableTypingFrontierToEventFlow_injective
        heq)

instance metacicDecidableTypingFrontierFieldFaithful :
    FieldFaithful MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicDecidableTypingFrontierFields
  field_faithful :=
    metacicDecidableTypingFrontierFields_faithful

instance metacicDecidableTypingFrontierNontrivial :
    Nontrivial MetaCICDecidableTypingFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICDecidableTypingFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICDecidableTypingFrontierUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetaCICDecidableTypingFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicDecidableTypingFrontierDecodeBHist
          (metacicDecidableTypingFrontierEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICDecidableTypingFrontierUp,
        metacicDecidableTypingFrontierFromEventFlow
            (metacicDecidableTypingFrontierToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICDecidableTypingFrontierUp,
          metacicDecidableTypingFrontierToEventFlow x =
              metacicDecidableTypingFrontierToEventFlow y →
            x = y) ∧
          metacicDecidableTypingFrontierEncodeBHist
            BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  have hdecode :
      ∀ h : BHist,
        metacicDecidableTypingFrontierDecodeBHist
            (metacicDecidableTypingFrontierEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have hround :
      ∀ x : MetaCICDecidableTypingFrontierUp,
        metacicDecidableTypingFrontierFromEventFlow
            (metacicDecidableTypingFrontierToEventFlow x) =
          some x := by
    intro x
    cases x with
    | mk inferType checkSame structuralEq boundedNormal refusal transport replay provenance
        localName =>
        change
          some
            (MetaCICDecidableTypingFrontierUp.mk
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  inferType))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  checkSame))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  structuralEq))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  boundedNormal))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  refusal))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  transport))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  replay))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  provenance))
              (metacicDecidableTypingFrontierDecodeBHist
                (metacicDecidableTypingFrontierEncodeBHist
                  localName))) =
            some
              (MetaCICDecidableTypingFrontierUp.mk inferType checkSame structuralEq
                boundedNormal refusal transport replay provenance localName)
        rw [hdecode inferType, hdecode checkSame, hdecode structuralEq, hdecode boundedNormal,
          hdecode refusal, hdecode transport, hdecode replay, hdecode provenance, hdecode localName]
  have hinj :
      ∀ x y : MetaCICDecidableTypingFrontierUp,
        metacicDecidableTypingFrontierToEventFlow x =
            metacicDecidableTypingFrontierToEventFlow y →
          x = y := by
    intro x y heq
    have hread :
        metacicDecidableTypingFrontierFromEventFlow
            (metacicDecidableTypingFrontierToEventFlow x) =
          metacicDecidableTypingFrontierFromEventFlow
            (metacicDecidableTypingFrontierToEventFlow y) :=
      congrArg metacicDecidableTypingFrontierFromEventFlow heq
    exact Option.some.inj (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact ⟨hdecode, hround, hinj, rfl⟩

end BEDC.Derived.MetaCICDecidableTypingFrontierUp
