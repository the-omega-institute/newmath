import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureResidueUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSignatureResidueUp : Type where
  | mk :
      (classifier signature gap residue witness transport replay provenance localName : BHist) →
      RealityConstrainedSignatureResidueUp
  deriving DecidableEq

def realityConstrainedSignatureResidueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSignatureResidueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSignatureResidueEncodeBHist h

def realityConstrainedSignatureResidueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSignatureResidueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSignatureResidueDecodeBHist tail)

private theorem realityConstrainedSignatureResidueDecode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedSignatureResidue_mk_congr
    {classifier classifier' signature signature' gap gap' residue residue' witness witness'
      transport transport' replay replay' provenance provenance' localName localName' : BHist}
    (hClassifier : classifier' = classifier)
    (hSignature : signature' = signature)
    (hGap : gap' = gap)
    (hResidue : residue' = residue)
    (hWitness : witness' = witness)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RealityConstrainedSignatureResidueUp.mk classifier' signature' gap' residue' witness'
        transport' replay' provenance' localName' =
      RealityConstrainedSignatureResidueUp.mk classifier signature gap residue witness
        transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hClassifier
  cases hSignature
  cases hGap
  cases hResidue
  cases hWitness
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def realityConstrainedSignatureResidueFields :
    RealityConstrainedSignatureResidueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureResidueUp.mk classifier signature gap residue witness transport
      replay provenance localName =>
      [classifier, signature, gap, residue, witness, transport, replay, provenance, localName]

def realityConstrainedSignatureResidueToEventFlow :
    RealityConstrainedSignatureResidueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realityConstrainedSignatureResidueFields x).map
        realityConstrainedSignatureResidueEncodeBHist

def realityConstrainedSignatureResidueFromEventFlow :
    EventFlow → Option RealityConstrainedSignatureResidueUp
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
  | classifier :: signature :: gap :: residue :: witness :: transport :: replay ::
      provenance :: localName :: [] =>
      some
        (RealityConstrainedSignatureResidueUp.mk
          (realityConstrainedSignatureResidueDecodeBHist classifier)
          (realityConstrainedSignatureResidueDecodeBHist signature)
          (realityConstrainedSignatureResidueDecodeBHist gap)
          (realityConstrainedSignatureResidueDecodeBHist residue)
          (realityConstrainedSignatureResidueDecodeBHist witness)
          (realityConstrainedSignatureResidueDecodeBHist transport)
          (realityConstrainedSignatureResidueDecodeBHist replay)
          (realityConstrainedSignatureResidueDecodeBHist provenance)
          (realityConstrainedSignatureResidueDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _rest => none

private theorem realityConstrainedSignatureResidue_round_trip :
    ∀ x : RealityConstrainedSignatureResidueUp,
      realityConstrainedSignatureResidueFromEventFlow
        (realityConstrainedSignatureResidueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk classifier signature gap residue witness transport replay provenance localName =>
      exact
        congrArg some
          (realityConstrainedSignatureResidue_mk_congr
            (realityConstrainedSignatureResidueDecode_encode_bhist classifier)
            (realityConstrainedSignatureResidueDecode_encode_bhist signature)
            (realityConstrainedSignatureResidueDecode_encode_bhist gap)
            (realityConstrainedSignatureResidueDecode_encode_bhist residue)
            (realityConstrainedSignatureResidueDecode_encode_bhist witness)
            (realityConstrainedSignatureResidueDecode_encode_bhist transport)
            (realityConstrainedSignatureResidueDecode_encode_bhist replay)
            (realityConstrainedSignatureResidueDecode_encode_bhist provenance)
            (realityConstrainedSignatureResidueDecode_encode_bhist localName))

private theorem realityConstrainedSignatureResidueToEventFlow_injective
    {x y : RealityConstrainedSignatureResidueUp} :
    realityConstrainedSignatureResidueToEventFlow x =
      realityConstrainedSignatureResidueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSignatureResidueFromEventFlow
          (realityConstrainedSignatureResidueToEventFlow x) =
        realityConstrainedSignatureResidueFromEventFlow
          (realityConstrainedSignatureResidueToEventFlow y) :=
    congrArg realityConstrainedSignatureResidueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedSignatureResidue_round_trip x).symm
      (Eq.trans hread (realityConstrainedSignatureResidue_round_trip y)))

private theorem realityConstrainedSignatureResidue_field_faithful :
    ∀ x y : RealityConstrainedSignatureResidueUp,
      realityConstrainedSignatureResidueFields x =
        realityConstrainedSignatureResidueFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk classifier signature gap residue witness transport replay provenance localName =>
      cases y with
      | mk classifier' signature' gap' residue' witness' transport' replay' provenance'
          localName' =>
          cases hfields
          rfl

instance realityConstrainedSignatureResidueBHistCarrier :
    BHistCarrier RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSignatureResidueToEventFlow
  fromEventFlow := realityConstrainedSignatureResidueFromEventFlow

instance realityConstrainedSignatureResidueChapterTasteGate :
    ChapterTasteGate RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSignatureResidueFromEventFlow
        (realityConstrainedSignatureResidueToEventFlow x) = some x
    exact realityConstrainedSignatureResidue_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSignatureResidueToEventFlow_injective heq)

instance realityConstrainedSignatureResidueFieldFaithful :
    FieldFaithful RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSignatureResidueFields
  field_faithful := realityConstrainedSignatureResidue_field_faithful

instance realityConstrainedSignatureResidueNontrivial :
    Nontrivial RealityConstrainedSignatureResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSignatureResidueUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSignatureResidueUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSignatureResidueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSignatureResidueChapterTasteGate

theorem RealityConstrainedSignatureResidueTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedSignatureResidueDecodeBHist
        (realityConstrainedSignatureResidueEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedSignatureResidueUp,
        realityConstrainedSignatureResidueFromEventFlow
          (realityConstrainedSignatureResidueToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedSignatureResidueUp,
          realityConstrainedSignatureResidueToEventFlow x =
            realityConstrainedSignatureResidueToEventFlow y → x = y) ∧
          (∀ (x : RealityConstrainedSignatureResidueUp) w m,
            List.Mem w (realityConstrainedSignatureResidueToEventFlow x) →
              List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) ∧
            realityConstrainedSignatureResidueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realityConstrainedSignatureResidueDecode_encode_bhist,
      realityConstrainedSignatureResidue_round_trip,
      (fun _ _ heq => realityConstrainedSignatureResidueToEventFlow_injective heq),
      (by
        intro _x _w m _hw _hm
        cases m with
        | b0 =>
            exact Or.inl rfl
        | b1 =>
            exact Or.inr rfl),
      rfl⟩

end BEDC.Derived.RealityConstrainedSignatureResidueUp.TasteGate
