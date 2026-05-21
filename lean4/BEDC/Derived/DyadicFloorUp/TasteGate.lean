import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicFloorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicFloorUp : Type where
  | mk (request scale floor successor lower upper modulus readback sealRow transport replay
      provenance name : BHist) : DyadicFloorUp
  deriving DecidableEq

def dyadicFloorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicFloorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicFloorEncodeBHist h

def dyadicFloorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicFloorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicFloorDecodeBHist tail)

private theorem dyadicFloor_decode_encode_bhist :
    ∀ h : BHist, dyadicFloorDecodeBHist (dyadicFloorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicFloorFields : DyadicFloorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicFloorUp.mk request scale floor successor lower upper modulus readback sealRow transport
      replay provenance name =>
      [request, scale, floor, successor, lower, upper, modulus, readback, sealRow, transport,
        replay, provenance, name]

def dyadicFloorToEventFlow : DyadicFloorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicFloorFields x).map dyadicFloorEncodeBHist

def dyadicFloorFromEventFlow : EventFlow → Option DyadicFloorUp
  -- BEDC touchpoint anchor: BHist BMark
  | request :: scale :: floor :: successor :: lower :: upper :: modulus :: readback ::
      sealRow :: transport :: replay :: provenance :: name :: [] =>
      some
        (DyadicFloorUp.mk
          (dyadicFloorDecodeBHist request)
          (dyadicFloorDecodeBHist scale)
          (dyadicFloorDecodeBHist floor)
          (dyadicFloorDecodeBHist successor)
          (dyadicFloorDecodeBHist lower)
          (dyadicFloorDecodeBHist upper)
          (dyadicFloorDecodeBHist modulus)
          (dyadicFloorDecodeBHist readback)
          (dyadicFloorDecodeBHist sealRow)
          (dyadicFloorDecodeBHist transport)
          (dyadicFloorDecodeBHist replay)
          (dyadicFloorDecodeBHist provenance)
          (dyadicFloorDecodeBHist name))
  | _ => none

private theorem dyadicFloor_round_trip :
    ∀ x : DyadicFloorUp,
      dyadicFloorFromEventFlow (dyadicFloorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request scale floor successor lower upper modulus readback sealRow transport replay
      provenance name =>
      simp only [dyadicFloorToEventFlow, dyadicFloorFields, dyadicFloorFromEventFlow,
        List.map_cons, List.map_nil, dyadicFloor_decode_encode_bhist]

private theorem dyadicFloorToEventFlow_injective {x y : DyadicFloorUp} :
    dyadicFloorToEventFlow x = dyadicFloorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicFloorFromEventFlow (dyadicFloorToEventFlow x) =
        dyadicFloorFromEventFlow (dyadicFloorToEventFlow y) :=
    congrArg dyadicFloorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicFloor_round_trip x).symm
      (Eq.trans hread (dyadicFloor_round_trip y)))

private theorem dyadicFloor_field_faithful :
    ∀ x y : DyadicFloorUp, dyadicFloorFields x = dyadicFloorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk request₁ scale₁ floor₁ successor₁ lower₁ upper₁ modulus₁ readback₁ sealRow₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk request₂ scale₂ floor₂ successor₂ lower₂ upper₂ modulus₂ readback₂ sealRow₂
          transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hrequest tail0
          injection tail0 with hscale tail1
          injection tail1 with hfloor tail2
          injection tail2 with hsuccessor tail3
          injection tail3 with hlower tail4
          injection tail4 with hupper tail5
          injection tail5 with hmodulus tail6
          injection tail6 with hreadback tail7
          injection tail7 with hseal tail8
          injection tail8 with htransport tail9
          injection tail9 with hreplay tail10
          injection tail10 with hprovenance tail11
          injection tail11 with hname _
          subst hrequest
          subst hscale
          subst hfloor
          subst hsuccessor
          subst hlower
          subst hupper
          subst hmodulus
          subst hreadback
          subst hseal
          subst htransport
          subst hreplay
          subst hprovenance
          subst hname
          rfl

instance dyadicFloorBHistCarrier : BHistCarrier DyadicFloorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicFloorToEventFlow
  fromEventFlow := dyadicFloorFromEventFlow

instance dyadicFloorChapterTasteGate : ChapterTasteGate DyadicFloorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicFloorFromEventFlow (dyadicFloorToEventFlow x) = some x
    exact dyadicFloor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicFloorToEventFlow_injective heq)

instance dyadicFloorFieldFaithful : FieldFaithful DyadicFloorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicFloorFields
  field_faithful := dyadicFloor_field_faithful

instance dyadicFloorNontrivial : Nontrivial DyadicFloorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicFloorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DyadicFloorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicFloorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicFloorChapterTasteGate

theorem DyadicFloorTasteGate_carrier_alignment
    (request scale floor successor lower upper modulus readback sealRow transport replay
      provenance name : BHist) :
    dyadicFloorFields
        (DyadicFloorUp.mk request scale floor successor lower upper modulus readback sealRow
          transport replay provenance name) =
      [request, scale, floor, successor, lower, upper, modulus, readback, sealRow, transport,
        replay, provenance, name] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  rfl

end BEDC.Derived.DyadicFloorUp
