import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachAlgebraUp : Type where
  | mk
      (ring norm banach productControl completionSeal transport replay provenance localName :
        BHist) :
      BanachAlgebraUp
  deriving DecidableEq

def BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h

def BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BanachAlgebraTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist
          (BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BanachAlgebraTasteGate_single_carrier_alignment_fields :
    BanachAlgebraUp -> List BHist
  | BanachAlgebraUp.mk ring norm banach productControl completionSeal transport replay
      provenance localName =>
      [ring, norm, banach, productControl, completionSeal, transport, replay, provenance,
        localName]

def BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow :
    BanachAlgebraUp -> EventFlow :=
  fun x =>
    (BanachAlgebraTasteGate_single_carrier_alignment_fields x).map
      BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist

def BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option BanachAlgebraUp
  | ring :: norm :: banach :: productControl :: completionSeal :: transport :: replay ::
      provenance :: localName :: [] =>
      some
        (BanachAlgebraUp.mk
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist ring)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist norm)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist banach)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist productControl)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist completionSeal)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist transport)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist replay)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist provenance)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist localName))
  | _ => none

private theorem BanachAlgebraTasteGate_single_carrier_alignment_round_trip :
    forall x : BanachAlgebraUp,
      BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
          (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  intro token
  cases token with
  | mk ring norm banach productControl completionSeal transport replay provenance localName =>
      simp only [BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow,
        BanachAlgebraTasteGate_single_carrier_alignment_fields,
        BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, BanachAlgebraTasteGate_single_carrier_alignment_decode_encode]

private theorem BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachAlgebraUp} :
    BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x =
        BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
            (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x) :=
        (BanachAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
            (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := BanachAlgebraTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem BanachAlgebraTasteGate_single_carrier_alignment_field_faithful :
    forall x y : BanachAlgebraUp,
      BanachAlgebraTasteGate_single_carrier_alignment_fields x =
          BanachAlgebraTasteGate_single_carrier_alignment_fields y ->
        x = y := by
  intro x y hfields
  cases x with
  | mk ring1 norm1 banach1 productControl1 completionSeal1 transport1 replay1
      provenance1 localName1 =>
      cases y with
      | mk ring2 norm2 banach2 productControl2 completionSeal2 transport2 replay2
          provenance2 localName2 =>
          cases hfields
          rfl

instance BanachAlgebraTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BanachAlgebraUp where
  toEventFlow := BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow

instance BanachAlgebraTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BanachAlgebraUp where
  round_trip := by
    intro x
    change
      BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
          (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BanachAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BanachAlgebraTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BanachAlgebraUp where
  fields := BanachAlgebraTasteGate_single_carrier_alignment_fields
  field_faithful := BanachAlgebraTasteGate_single_carrier_alignment_field_faithful

instance BanachAlgebraTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial BanachAlgebraUp where
  witness_pair :=
    ⟨BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BanachAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def BanachAlgebraTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BanachAlgebraUp :=
  BanachAlgebraTasteGate_single_carrier_alignment_ChapterTasteGate

theorem BanachAlgebraTasteGate_single_carrier_alignment :
    (forall h : BHist,
      BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist
          (BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      BanachAlgebraTasteGate_single_carrier_alignment_fields
          (BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  exact ⟨BanachAlgebraTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.BanachAlgebraUp
