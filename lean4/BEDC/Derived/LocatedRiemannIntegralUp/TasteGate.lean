import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRiemannIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRiemannIntegralUp : Type where
  | mk :
      (interval mesh sum regulated dyadic window readback realSeal transport replay provenance
        name : BHist) →
      LocatedRiemannIntegralUp
  deriving DecidableEq

def locatedRiemannIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRiemannIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRiemannIntegralEncodeBHist h

def locatedRiemannIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRiemannIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRiemannIntegralDecodeBHist tail)

private theorem locatedRiemannIntegral_decode_encode_bhist :
    ∀ h : BHist,
      locatedRiemannIntegralDecodeBHist (locatedRiemannIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedRiemannIntegralFields : LocatedRiemannIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRiemannIntegralUp.mk interval mesh sum regulated dyadic window readback realSeal
      transport replay provenance name =>
      [interval, mesh, sum, regulated, dyadic, window, readback, realSeal, transport, replay,
        provenance, name]

def locatedRiemannIntegralToEventFlow : LocatedRiemannIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRiemannIntegralFields x).map locatedRiemannIntegralEncodeBHist

def locatedRiemannIntegralFromEventFlow : EventFlow → Option LocatedRiemannIntegralUp
  -- BEDC touchpoint anchor: BHist BMark
  | interval :: mesh :: sum :: regulated :: dyadic :: window :: readback :: realSeal ::
      transport :: replay :: provenance :: name :: [] =>
      some
        (LocatedRiemannIntegralUp.mk
          (locatedRiemannIntegralDecodeBHist interval)
          (locatedRiemannIntegralDecodeBHist mesh)
          (locatedRiemannIntegralDecodeBHist sum)
          (locatedRiemannIntegralDecodeBHist regulated)
          (locatedRiemannIntegralDecodeBHist dyadic)
          (locatedRiemannIntegralDecodeBHist window)
          (locatedRiemannIntegralDecodeBHist readback)
          (locatedRiemannIntegralDecodeBHist realSeal)
          (locatedRiemannIntegralDecodeBHist transport)
          (locatedRiemannIntegralDecodeBHist replay)
          (locatedRiemannIntegralDecodeBHist provenance)
          (locatedRiemannIntegralDecodeBHist name))
  | _ => none

private theorem locatedRiemannIntegral_round_trip :
    ∀ x : LocatedRiemannIntegralUp,
      locatedRiemannIntegralFromEventFlow (locatedRiemannIntegralToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval mesh sum regulated dyadic window readback realSeal transport replay provenance
      name =>
      simp only [locatedRiemannIntegralToEventFlow, locatedRiemannIntegralFields,
        locatedRiemannIntegralFromEventFlow, List.map_cons, List.map_nil,
        locatedRiemannIntegral_decode_encode_bhist]

private theorem locatedRiemannIntegralToEventFlow_injective
    {x y : LocatedRiemannIntegralUp} :
    locatedRiemannIntegralToEventFlow x = locatedRiemannIntegralToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRiemannIntegralFromEventFlow (locatedRiemannIntegralToEventFlow x) =
        locatedRiemannIntegralFromEventFlow (locatedRiemannIntegralToEventFlow y) :=
    congrArg locatedRiemannIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRiemannIntegral_round_trip x).symm
      (Eq.trans hread (locatedRiemannIntegral_round_trip y)))

private theorem locatedRiemannIntegral_field_faithful :
    ∀ x y : LocatedRiemannIntegralUp,
      locatedRiemannIntegralFields x = locatedRiemannIntegralFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval₁ mesh₁ sum₁ regulated₁ dyadic₁ window₁ readback₁ realSeal₁ transport₁
      replay₁ provenance₁ name₁ =>
      cases y with
      | mk interval₂ mesh₂ sum₂ regulated₂ dyadic₂ window₂ readback₂ realSeal₂ transport₂
          replay₂ provenance₂ name₂ =>
          injection hfields with hinterval tail0
          injection tail0 with hmesh tail1
          injection tail1 with hsum tail2
          injection tail2 with hregulated tail3
          injection tail3 with hdyadic tail4
          injection tail4 with hwindow tail5
          injection tail5 with hreadback tail6
          injection tail6 with hseal tail7
          injection tail7 with htransport tail8
          injection tail8 with hreplay tail9
          injection tail9 with hprovenance tail10
          injection tail10 with hname _
          subst hinterval
          subst hmesh
          subst hsum
          subst hregulated
          subst hdyadic
          subst hwindow
          subst hreadback
          subst hseal
          subst htransport
          subst hreplay
          subst hprovenance
          subst hname
          rfl

instance locatedRiemannIntegralBHistCarrier :
    BHistCarrier LocatedRiemannIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRiemannIntegralToEventFlow
  fromEventFlow := locatedRiemannIntegralFromEventFlow

instance locatedRiemannIntegralChapterTasteGate :
    ChapterTasteGate LocatedRiemannIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRiemannIntegralFromEventFlow (locatedRiemannIntegralToEventFlow x) =
        some x
    exact locatedRiemannIntegral_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRiemannIntegralToEventFlow_injective heq)

instance locatedRiemannIntegralFieldFaithful :
    FieldFaithful LocatedRiemannIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRiemannIntegralFields
  field_faithful := locatedRiemannIntegral_field_faithful

def taste_gate : ChapterTasteGate LocatedRiemannIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRiemannIntegralChapterTasteGate

end BEDC.Derived.LocatedRiemannIntegralUp
