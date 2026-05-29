import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OneSidedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OneSidedLimitUp : Type where
  | mk
      (approach side windows schedule readback tolerance realSeal transport replay provenance
        localName : BHist) :
        OneSidedLimitUp
  deriving DecidableEq

def oneSidedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oneSidedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oneSidedLimitEncodeBHist h

def oneSidedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oneSidedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oneSidedLimitDecodeBHist tail)

private theorem OneSidedLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oneSidedLimitFields : OneSidedLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OneSidedLimitUp.mk approach side windows schedule readback tolerance realSeal transport
      replay provenance localName =>
      [approach, side, windows, schedule, readback, tolerance, realSeal, transport, replay,
        provenance, localName]

def oneSidedLimitToEventFlow : OneSidedLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oneSidedLimitFields x).map oneSidedLimitEncodeBHist

private def OneSidedLimitTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      OneSidedLimitTasteGate_single_carrier_alignment_eventAt index rest

def oneSidedLimitFromEventFlow : EventFlow → Option OneSidedLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (OneSidedLimitUp.mk
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 0 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 1 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 2 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 3 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 4 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 5 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 6 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 7 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 8 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 9 ef))
          (oneSidedLimitDecodeBHist
            (OneSidedLimitTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem OneSidedLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OneSidedLimitUp,
      oneSidedLimitFromEventFlow (oneSidedLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk approach side windows schedule readback tolerance realSeal transport replay provenance
      localName =>
      change
        some
          (OneSidedLimitUp.mk
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist approach))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist side))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist windows))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist schedule))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist readback))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist tolerance))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist realSeal))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist transport))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist replay))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist provenance))
            (oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist localName))) =
          some
            (OneSidedLimitUp.mk approach side windows schedule readback tolerance realSeal
              transport replay provenance localName)
      rw [OneSidedLimitTasteGate_single_carrier_alignment_decode_encode approach,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode side,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode windows,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode schedule,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode readback,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode tolerance,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode realSeal,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode transport,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode replay,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode provenance,
        OneSidedLimitTasteGate_single_carrier_alignment_decode_encode localName]

private theorem OneSidedLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OneSidedLimitUp} :
    oneSidedLimitToEventFlow x = oneSidedLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oneSidedLimitFromEventFlow (oneSidedLimitToEventFlow x) =
        oneSidedLimitFromEventFlow (oneSidedLimitToEventFlow y) :=
    congrArg oneSidedLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OneSidedLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OneSidedLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem OneSidedLimitTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : OneSidedLimitUp, oneSidedLimitFields x = oneSidedLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk approach₁ side₁ windows₁ schedule₁ readback₁ tolerance₁ realSeal₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk approach₂ side₂ windows₂ schedule₂ readback₂ tolerance₂ realSeal₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection hfields with happroach tail0
          injection tail0 with hside tail1
          injection tail1 with hwindows tail2
          injection tail2 with hschedule tail3
          injection tail3 with hreadback tail4
          injection tail4 with htolerance tail5
          injection tail5 with hrealSeal tail6
          injection tail6 with htransport tail7
          injection tail7 with hreplay tail8
          injection tail8 with hprovenance tail9
          injection tail9 with hlocalName _
          subst happroach
          subst hside
          subst hwindows
          subst hschedule
          subst hreadback
          subst htolerance
          subst hrealSeal
          subst htransport
          subst hreplay
          subst hprovenance
          subst hlocalName
          rfl

instance oneSidedLimitBHistCarrier : BHistCarrier OneSidedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oneSidedLimitToEventFlow
  fromEventFlow := oneSidedLimitFromEventFlow

instance oneSidedLimitChapterTasteGate : ChapterTasteGate OneSidedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oneSidedLimitFromEventFlow (oneSidedLimitToEventFlow x) = some x
    exact OneSidedLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OneSidedLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance oneSidedLimitFieldFaithful : FieldFaithful OneSidedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := oneSidedLimitFields
  field_faithful := OneSidedLimitTasteGate_single_carrier_alignment_fields_faithful

instance oneSidedLimitNontrivial : Nontrivial OneSidedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OneSidedLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OneSidedLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OneSidedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oneSidedLimitChapterTasteGate

theorem OneSidedLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, oneSidedLimitDecodeBHist (oneSidedLimitEncodeBHist h) = h) ∧
      (∀ x : OneSidedLimitUp,
        oneSidedLimitFromEventFlow (oneSidedLimitToEventFlow x) = some x) ∧
      (∀ x y : OneSidedLimitUp,
        oneSidedLimitToEventFlow x = oneSidedLimitToEventFlow y → x = y) ∧
      oneSidedLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · exact OneSidedLimitTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact OneSidedLimitTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact OneSidedLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.OneSidedLimitUp
