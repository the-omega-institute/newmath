import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionEnvelopeUp : Type where
  | mk
      (window tolerance readback realSeal completionRoute transport replay provenance
        localName : BHist) :
        RegularCauchyCompletionEnvelopeUp
  deriving DecidableEq

def regularCauchyCompletionEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionEnvelopeEncodeBHist h

def regularCauchyCompletionEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionEnvelopeDecodeBHist tail)

private theorem RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyCompletionEnvelopeDecodeBHist
          (regularCauchyCompletionEnvelopeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionEnvelopeFields :
    RegularCauchyCompletionEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionEnvelopeUp.mk window tolerance readback realSeal completionRoute
      transport replay provenance localName =>
      [window, tolerance, readback, realSeal, completionRoute, transport, replay, provenance,
        localName]

def regularCauchyCompletionEnvelopeToEventFlow :
    RegularCauchyCompletionEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyCompletionEnvelopeFields x).map
      regularCauchyCompletionEnvelopeEncodeBHist

private def RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt index rest

def regularCauchyCompletionEnvelopeFromEventFlow :
    EventFlow → Option RegularCauchyCompletionEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyCompletionEnvelopeUp.mk
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 0 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 1 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 2 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 3 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 4 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 5 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 6 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 7 ef))
          (regularCauchyCompletionEnvelopeDecodeBHist
            (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompletionEnvelopeUp,
      regularCauchyCompletionEnvelopeFromEventFlow
          (regularCauchyCompletionEnvelopeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window tolerance readback realSeal completionRoute transport replay provenance localName =>
      change
        some
          (RegularCauchyCompletionEnvelopeUp.mk
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist window))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist tolerance))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist readback))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist realSeal))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist completionRoute))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist transport))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist replay))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist provenance))
            (regularCauchyCompletionEnvelopeDecodeBHist
              (regularCauchyCompletionEnvelopeEncodeBHist localName))) =
          some
            (RegularCauchyCompletionEnvelopeUp.mk window tolerance readback realSeal
              completionRoute transport replay provenance localName)
      rw [RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode window,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode tolerance,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode readback,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode realSeal,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode
          completionRoute,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode transport,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode replay,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode provenance,
        RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode localName]

private theorem RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionEnvelopeUp} :
    regularCauchyCompletionEnvelopeToEventFlow x =
        regularCauchyCompletionEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionEnvelopeFromEventFlow
          (regularCauchyCompletionEnvelopeToEventFlow x) =
        regularCauchyCompletionEnvelopeFromEventFlow
          (regularCauchyCompletionEnvelopeToEventFlow y) :=
    congrArg regularCauchyCompletionEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyCompletionEnvelopeUp,
      regularCauchyCompletionEnvelopeFields x = regularCauchyCompletionEnvelopeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk window₁ tolerance₁ readback₁ realSeal₁ completionRoute₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk window₂ tolerance₂ readback₂ realSeal₂ completionRoute₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection hfields with hwindow tail0
          injection tail0 with htolerance tail1
          injection tail1 with hreadback tail2
          injection tail2 with hrealSeal tail3
          injection tail3 with hcompletionRoute tail4
          injection tail4 with htransport tail5
          injection tail5 with hreplay tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hlocalName _
          subst hwindow
          subst htolerance
          subst hreadback
          subst hrealSeal
          subst hcompletionRoute
          subst htransport
          subst hreplay
          subst hprovenance
          subst hlocalName
          rfl

instance regularCauchyCompletionEnvelopeBHistCarrier :
    BHistCarrier RegularCauchyCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionEnvelopeToEventFlow
  fromEventFlow := regularCauchyCompletionEnvelopeFromEventFlow

instance regularCauchyCompletionEnvelopeChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionEnvelopeFromEventFlow
          (regularCauchyCompletionEnvelopeToEventFlow x) =
        some x
    exact RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyCompletionEnvelopeFieldFaithful :
    FieldFaithful RegularCauchyCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompletionEnvelopeFields
  field_faithful :=
    RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyCompletionEnvelopeNontrivial :
    Nontrivial RegularCauchyCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCompletionEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCompletionEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionEnvelopeChapterTasteGate

theorem RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionEnvelopeDecodeBHist
          (regularCauchyCompletionEnvelopeEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyCompletionEnvelopeUp,
        regularCauchyCompletionEnvelopeFromEventFlow
            (regularCauchyCompletionEnvelopeToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyCompletionEnvelopeUp,
        regularCauchyCompletionEnvelopeToEventFlow x =
            regularCauchyCompletionEnvelopeToEventFlow y →
          x = y) ∧
      regularCauchyCompletionEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · exact RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          RegularCauchyCompletionEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.RegularCauchyCompletionEnvelopeUp
