import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedLimitUp : Type where
  | mk (sequence modulus schedule readback sealRow transport replay provenance name : BHist) :
      LocatedLimitUp
  deriving DecidableEq

def locatedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedLimitEncodeBHist h

def locatedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedLimitDecodeBHist tail)

private theorem locatedLimit_decode_encode_bhist :
    ∀ h : BHist, locatedLimitDecodeBHist (locatedLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedLimitFields : LocatedLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay provenance name =>
      [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance, name]

def locatedLimitToEventFlow : LocatedLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedLimitFields x).map locatedLimitEncodeBHist

def locatedLimitFromEventFlow : EventFlow → Option LocatedLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | sequence :: modulus :: schedule :: readback :: sealRow :: transport :: replay ::
      provenance :: name :: [] =>
      some
        (LocatedLimitUp.mk
          (locatedLimitDecodeBHist sequence)
          (locatedLimitDecodeBHist modulus)
          (locatedLimitDecodeBHist schedule)
          (locatedLimitDecodeBHist readback)
          (locatedLimitDecodeBHist sealRow)
          (locatedLimitDecodeBHist transport)
          (locatedLimitDecodeBHist replay)
          (locatedLimitDecodeBHist provenance)
          (locatedLimitDecodeBHist name))
  | _ => none

private theorem locatedLimit_round_trip :
    ∀ x : LocatedLimitUp,
      locatedLimitFromEventFlow (locatedLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sequence modulus schedule readback sealRow transport replay provenance name =>
      simp only [locatedLimitToEventFlow, locatedLimitFields, locatedLimitFromEventFlow,
        List.map_cons, List.map_nil, locatedLimit_decode_encode_bhist]

private theorem locatedLimitToEventFlow_injective {x y : LocatedLimitUp} :
    locatedLimitToEventFlow x = locatedLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedLimitFromEventFlow (locatedLimitToEventFlow x) =
        locatedLimitFromEventFlow (locatedLimitToEventFlow y) :=
    congrArg locatedLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedLimit_round_trip x).symm
      (Eq.trans hread (locatedLimit_round_trip y)))

private theorem locatedLimit_field_faithful :
    ∀ x y : LocatedLimitUp, locatedLimitFields x = locatedLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sequence₁ modulus₁ schedule₁ readback₁ sealRow₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk sequence₂ modulus₂ schedule₂ readback₂ sealRow₂ transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hsequence tail0
          injection tail0 with hmodulus tail1
          injection tail1 with hschedule tail2
          injection tail2 with hreadback tail3
          injection tail3 with hseal tail4
          injection tail4 with htransport tail5
          injection tail5 with hreplay tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hname _
          subst hsequence
          subst hmodulus
          subst hschedule
          subst hreadback
          subst hseal
          subst htransport
          subst hreplay
          subst hprovenance
          subst hname
          rfl

instance locatedLimitBHistCarrier : BHistCarrier LocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedLimitToEventFlow
  fromEventFlow := locatedLimitFromEventFlow

instance locatedLimitChapterTasteGate : ChapterTasteGate LocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedLimitFromEventFlow (locatedLimitToEventFlow x) = some x
    exact locatedLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedLimitToEventFlow_injective heq)

instance locatedLimitFieldFaithful : FieldFaithful LocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedLimitFields
  field_faithful := locatedLimit_field_faithful

instance locatedLimitNontrivial : Nontrivial LocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedLimitChapterTasteGate

theorem LocatedLimitTasteGate_carrier_alignment
    (sequence modulus schedule readback sealRow transport replay provenance name : BHist) :
    locatedLimitFields
        (LocatedLimitUp.mk sequence modulus schedule readback sealRow transport replay provenance
          name) =
      [sequence, modulus, schedule, readback, sealRow, transport, replay, provenance, name] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  rfl

end BEDC.Derived.LocatedLimitUp
