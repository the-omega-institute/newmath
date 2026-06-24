import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalizedCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalizedCauchySubsequenceUp : Type where
  | mk
      (window stream readback dyadic bolzano endpoint transport replay provenance localName :
        BHist) :
      LocalizedCauchySubsequenceUp
  deriving DecidableEq

def LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_encodeBHist h

def LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields :
    LocalizedCauchySubsequenceUp -> List BHist
  | LocalizedCauchySubsequenceUp.mk window stream readback dyadic bolzano endpoint
      transport replay provenance localName =>
      [window, stream, readback, dyadic, bolzano, endpoint, transport, replay, provenance,
        localName]

def LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow :
    LocalizedCauchySubsequenceUp -> EventFlow :=
  fun x =>
    (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields x).map
      LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_encodeBHist

def LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option LocalizedCauchySubsequenceUp
  | window :: stream :: readback :: dyadic :: bolzano :: endpoint :: transport :: replay ::
      provenance :: localName :: [] =>
      some
        (LocalizedCauchySubsequenceUp.mk
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist window)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist stream)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist readback)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist dyadic)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist bolzano)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist endpoint)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist transport)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist replay)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist provenance)
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist localName))
  | _ => none

private theorem LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_round_trip :
    forall x : LocalizedCauchySubsequenceUp,
      LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk window stream readback dyadic bolzano endpoint transport replay provenance localName =>
      simp only [LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow,
        LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields,
        LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow,
        List.map_cons, List.map_nil,
        LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode]

private theorem
    LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocalizedCauchySubsequenceUp} :
    LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow x =
        LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow
            (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow x) :=
        (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow
            (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_field_faithful :
    forall x y : LocalizedCauchySubsequenceUp,
      LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields x =
          LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk window1 stream1 readback1 dyadic1 bolzano1 endpoint1 transport1 replay1
      provenance1 localName1 =>
      cases y with
      | mk window2 stream2 readback2 dyadic2 bolzano2 endpoint2 transport2 replay2
          provenance2 localName2 =>
          cases hfields
          rfl

instance LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier LocalizedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow

instance LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate LocalizedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fromEventFlow
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful LocalizedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields
  field_faithful :=
    LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_field_faithful

instance LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial LocalizedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocalizedCauchySubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocalizedCauchySubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocalizedCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_ChapterTasteGate

theorem LocalizedCauchySubsequenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decodeBHist
          (LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
        LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_fields
            (LocalizedCauchySubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocalizedCauchySubsequenceTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.LocalizedCauchySubsequenceUp
