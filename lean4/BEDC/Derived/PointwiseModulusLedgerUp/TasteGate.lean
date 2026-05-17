import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointwiseModulusLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointwiseModulusLedgerUp : Type where
  | mk :
      (source target graph center tolerance radius implication transport route provenance
        localName : BHist) →
        PointwiseModulusLedgerUp
  deriving DecidableEq

def pointwiseModulusLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointwiseModulusLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointwiseModulusLedgerEncodeBHist h

def pointwiseModulusLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointwiseModulusLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointwiseModulusLedgerDecodeBHist tail)

private theorem PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def pointwiseModulusLedgerFields : PointwiseModulusLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PointwiseModulusLedgerUp.mk source target graph center tolerance radius implication
      transport route provenance localName =>
      [source, target, graph, center, tolerance, radius, implication, transport, route,
        provenance, localName]

def pointwiseModulusLedgerToEventFlow : PointwiseModulusLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (pointwiseModulusLedgerFields x).map pointwiseModulusLedgerEncodeBHist

def pointwiseModulusLedgerFromEventFlow : EventFlow → Option PointwiseModulusLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | source :: target :: graph :: center :: tolerance :: radius :: implication :: transport ::
      route :: provenance :: localName :: [] =>
      some
        (PointwiseModulusLedgerUp.mk
          (pointwiseModulusLedgerDecodeBHist source)
          (pointwiseModulusLedgerDecodeBHist target)
          (pointwiseModulusLedgerDecodeBHist graph)
          (pointwiseModulusLedgerDecodeBHist center)
          (pointwiseModulusLedgerDecodeBHist tolerance)
          (pointwiseModulusLedgerDecodeBHist radius)
          (pointwiseModulusLedgerDecodeBHist implication)
          (pointwiseModulusLedgerDecodeBHist transport)
          (pointwiseModulusLedgerDecodeBHist route)
          (pointwiseModulusLedgerDecodeBHist provenance)
          (pointwiseModulusLedgerDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l ::
      _rest => none

private theorem PointwiseModulusLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PointwiseModulusLedgerUp,
      pointwiseModulusLedgerFromEventFlow (pointwiseModulusLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target graph center tolerance radius implication transport route provenance
      localName =>
      change
        some
          (PointwiseModulusLedgerUp.mk
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist source))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist target))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist graph))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist center))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist tolerance))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist radius))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist implication))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist transport))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist route))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist provenance))
            (pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist localName))) =
          some
            (PointwiseModulusLedgerUp.mk source target graph center tolerance radius implication
              transport route provenance localName)
      rw [PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode source,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode target,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode graph,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode center,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode tolerance,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode radius,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode implication,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode transport,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode route,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode provenance,
        PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode localName]

private theorem PointwiseModulusLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PointwiseModulusLedgerUp} :
    pointwiseModulusLedgerToEventFlow x = pointwiseModulusLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointwiseModulusLedgerFromEventFlow (pointwiseModulusLedgerToEventFlow x) =
        pointwiseModulusLedgerFromEventFlow (pointwiseModulusLedgerToEventFlow y) :=
    congrArg pointwiseModulusLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PointwiseModulusLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PointwiseModulusLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem PointwiseModulusLedgerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PointwiseModulusLedgerUp,
      pointwiseModulusLedgerFields x = pointwiseModulusLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ target₁ graph₁ center₁ tolerance₁ radius₁ implication₁ transport₁ route₁
      provenance₁ localName₁ =>
      cases y with
      | mk source₂ target₂ graph₂ center₂ tolerance₂ radius₂ implication₂ transport₂ route₂
          provenance₂ localName₂ =>
          injection hfields with hSource tail0
          injection tail0 with hTarget tail1
          injection tail1 with hGraph tail2
          injection tail2 with hCenter tail3
          injection tail3 with hTolerance tail4
          injection tail4 with hRadius tail5
          injection tail5 with hImplication tail6
          injection tail6 with hTransport tail7
          injection tail7 with hRoute tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hSource
          subst hTarget
          subst hGraph
          subst hCenter
          subst hTolerance
          subst hRadius
          subst hImplication
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hLocalName
          rfl

instance pointwiseModulusLedgerBHistCarrier : BHistCarrier PointwiseModulusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointwiseModulusLedgerToEventFlow
  fromEventFlow := pointwiseModulusLedgerFromEventFlow

instance pointwiseModulusLedgerChapterTasteGate : ChapterTasteGate PointwiseModulusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pointwiseModulusLedgerFromEventFlow (pointwiseModulusLedgerToEventFlow x) = some x
    exact PointwiseModulusLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PointwiseModulusLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance pointwiseModulusLedgerFieldFaithful : FieldFaithful PointwiseModulusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pointwiseModulusLedgerFields
  field_faithful := PointwiseModulusLedgerTasteGate_single_carrier_alignment_fields_faithful

instance pointwiseModulusLedgerNontrivial : Nontrivial PointwiseModulusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PointwiseModulusLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PointwiseModulusLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem PointwiseModulusLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      pointwiseModulusLedgerDecodeBHist (pointwiseModulusLedgerEncodeBHist h) = h) ∧
      Nonempty (Nontrivial PointwiseModulusLedgerUp) ∧
        Nonempty (ChapterTasteGate PointwiseModulusLedgerUp) ∧
          Nonempty (FieldFaithful PointwiseModulusLedgerUp) ∧
            pointwiseModulusLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PointwiseModulusLedgerTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨pointwiseModulusLedgerNontrivial⟩
    · constructor
      · exact ⟨pointwiseModulusLedgerChapterTasteGate⟩
      · constructor
        · exact ⟨pointwiseModulusLedgerFieldFaithful⟩
        · rfl

end BEDC.Derived.PointwiseModulusLedgerUp.TasteGate
