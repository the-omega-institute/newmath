import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusNormalizerUp : Type where
  | mk :
      (x y muX muY meet window dyadic readback sealRow transport route provenance
        name : BHist) →
        RegularCauchyModulusNormalizerUp
  deriving DecidableEq

def regularCauchyModulusNormalizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusNormalizerEncodeBHist h

def regularCauchyModulusNormalizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusNormalizerDecodeBHist tail)

private theorem regularCauchyModulusNormalizer_decode_encode :
    ∀ h : BHist,
      regularCauchyModulusNormalizerDecodeBHist
          (regularCauchyModulusNormalizerEncodeBHist h) =
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

def regularCauchyModulusNormalizerFields :
    RegularCauchyModulusNormalizerUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyModulusNormalizerUp.mk x y muX muY meet window dyadic readback sealRow
      transport route provenance name =>
      [x, y, muX, muY, meet, window, dyadic, readback, sealRow, transport, route,
        provenance, name]

def regularCauchyModulusNormalizerToEventFlow :
    RegularCauchyModulusNormalizerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyModulusNormalizerFields x).map regularCauchyModulusNormalizerEncodeBHist

def regularCauchyModulusNormalizerFromEventFlow :
    EventFlow → Option RegularCauchyModulusNormalizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | x :: y :: muX :: muY :: meet :: window :: dyadic :: readback :: sealRow ::
      transport :: route :: provenance :: name :: [] =>
      some
        (RegularCauchyModulusNormalizerUp.mk
          (regularCauchyModulusNormalizerDecodeBHist x)
          (regularCauchyModulusNormalizerDecodeBHist y)
          (regularCauchyModulusNormalizerDecodeBHist muX)
          (regularCauchyModulusNormalizerDecodeBHist muY)
          (regularCauchyModulusNormalizerDecodeBHist meet)
          (regularCauchyModulusNormalizerDecodeBHist window)
          (regularCauchyModulusNormalizerDecodeBHist dyadic)
          (regularCauchyModulusNormalizerDecodeBHist readback)
          (regularCauchyModulusNormalizerDecodeBHist sealRow)
          (regularCauchyModulusNormalizerDecodeBHist transport)
          (regularCauchyModulusNormalizerDecodeBHist route)
          (regularCauchyModulusNormalizerDecodeBHist provenance)
          (regularCauchyModulusNormalizerDecodeBHist name))
  | _ => none

private theorem regularCauchyModulusNormalizer_round_trip :
    ∀ x : RegularCauchyModulusNormalizerUp,
      regularCauchyModulusNormalizerFromEventFlow
          (regularCauchyModulusNormalizerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk x y muX muY meet window dyadic readback sealRow transport route provenance name =>
      simp only [regularCauchyModulusNormalizerToEventFlow,
        regularCauchyModulusNormalizerFields, regularCauchyModulusNormalizerFromEventFlow,
        List.map_cons, List.map_nil, regularCauchyModulusNormalizer_decode_encode]

private theorem regularCauchyModulusNormalizerToEventFlow_injective
    {x y : RegularCauchyModulusNormalizerUp} :
    regularCauchyModulusNormalizerToEventFlow x =
        regularCauchyModulusNormalizerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyModulusNormalizerFromEventFlow
            (regularCauchyModulusNormalizerToEventFlow x) :=
        (regularCauchyModulusNormalizer_round_trip x).symm
      _ =
          regularCauchyModulusNormalizerFromEventFlow
            (regularCauchyModulusNormalizerToEventFlow y) :=
        congrArg regularCauchyModulusNormalizerFromEventFlow hxy
      _ = some y := regularCauchyModulusNormalizer_round_trip y
  exact Option.some.inj optionEq

private theorem regularCauchyModulusNormalizer_field_faithful :
    ∀ x y : RegularCauchyModulusNormalizerUp,
      regularCauchyModulusNormalizerFields x = regularCauchyModulusNormalizerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk x₁ y₁ muX₁ muY₁ meet₁ window₁ dyadic₁ readback₁ sealRow₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk x₂ y₂ muX₂ muY₂ meet₂ window₂ dyadic₂ readback₂ sealRow₂ transport₂ route₂
          provenance₂ name₂ =>
          injection hfields with hx tail0
          injection tail0 with hy tail1
          injection tail1 with hmuX tail2
          injection tail2 with hmuY tail3
          injection tail3 with hmeet tail4
          injection tail4 with hwindow tail5
          injection tail5 with hdyadic tail6
          injection tail6 with hreadback tail7
          injection tail7 with hsealRow tail8
          injection tail8 with htransport tail9
          injection tail9 with hroute tail10
          injection tail10 with hprovenance tail11
          injection tail11 with hname _
          subst hx
          subst hy
          subst hmuX
          subst hmuY
          subst hmeet
          subst hwindow
          subst hdyadic
          subst hreadback
          subst hsealRow
          subst htransport
          subst hroute
          subst hprovenance
          subst hname
          rfl

instance regularCauchyModulusNormalizerBHistCarrier :
    BHistCarrier RegularCauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusNormalizerToEventFlow
  fromEventFlow := regularCauchyModulusNormalizerFromEventFlow

instance regularCauchyModulusNormalizerChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusNormalizerFromEventFlow
          (regularCauchyModulusNormalizerToEventFlow x) =
        some x
    exact regularCauchyModulusNormalizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyModulusNormalizerToEventFlow_injective heq)

instance regularCauchyModulusNormalizerFieldFaithful :
    FieldFaithful RegularCauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyModulusNormalizerFields
  field_faithful := regularCauchyModulusNormalizer_field_faithful

instance regularCauchyModulusNormalizerNontrivial :
    Nontrivial RegularCauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyModulusNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyModulusNormalizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyModulusNormalizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyModulusNormalizerChapterTasteGate

theorem RegularCauchyModulusNormalizerTasteGate_single_carrier_alignment :
    Nonempty RegularCauchyModulusNormalizerUp ∧
      regularCauchyModulusNormalizerFields
          (RegularCauchyModulusNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact
      ⟨RegularCauchyModulusNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty⟩
  · rfl

end BEDC.Derived.RegularCauchyModulusNormalizerUp
