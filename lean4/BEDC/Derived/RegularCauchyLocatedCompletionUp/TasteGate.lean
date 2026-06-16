import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedCompletionUp : Type where
  | mk (stream regular dyadic located completion realSeal transport replay provenance
      localName : BHist) : RegularCauchyLocatedCompletionUp
  deriving DecidableEq

def regularCauchyLocatedCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedCompletionEncodeBHist h

def regularCauchyLocatedCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedCompletionDecodeBHist tail)

private theorem RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyLocatedCompletionDecodeBHist
        (regularCauchyLocatedCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyLocatedCompletionFields :
    RegularCauchyLocatedCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedCompletionUp.mk stream regular dyadic located completion realSeal
      transport replay provenance localName =>
      [stream, regular, dyadic, located, completion, realSeal, transport, replay, provenance,
        localName]

def regularCauchyLocatedCompletionToEventFlow :
    RegularCauchyLocatedCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyLocatedCompletionFields x).map
      regularCauchyLocatedCompletionEncodeBHist

def regularCauchyLocatedCompletionFromEventFlow :
    EventFlow → Option RegularCauchyLocatedCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | stream :: restStream =>
      match restStream with
      | regular :: restRegular =>
          match restRegular with
          | dyadic :: restDyadic =>
              match restDyadic with
              | located :: restLocated =>
                  match restLocated with
                  | completion :: restCompletion =>
                      match restCompletion with
                      | realSeal :: restRealSeal =>
                          match restRealSeal with
                          | transport :: restTransport =>
                              match restTransport with
                              | replay :: restReplay =>
                                  match restReplay with
                                  | provenance :: restProvenance =>
                                      match restProvenance with
                                      | localName :: restLocalName =>
                                          match restLocalName with
                                          | [] =>
                                              some
                                                (RegularCauchyLocatedCompletionUp.mk
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    stream)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    regular)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    dyadic)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    located)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    completion)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    realSeal)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    transport)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    replay)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    provenance)
                                                  (regularCauchyLocatedCompletionDecodeBHist
                                                    localName))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyLocatedCompletionUp,
      regularCauchyLocatedCompletionFromEventFlow
        (regularCauchyLocatedCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream regular dyadic located completion realSeal transport replay provenance
      localName =>
      change
        some
          (RegularCauchyLocatedCompletionUp.mk
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist stream))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist regular))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist dyadic))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist located))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist completion))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist realSeal))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist transport))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist replay))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist provenance))
            (regularCauchyLocatedCompletionDecodeBHist
              (regularCauchyLocatedCompletionEncodeBHist localName))) =
          some
            (RegularCauchyLocatedCompletionUp.mk stream regular dyadic located completion
              realSeal transport replay provenance localName)
      rw [RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode stream,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode regular,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode dyadic,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode located,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode completion,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode realSeal,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode transport,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode replay,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode provenance,
        RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyLocatedCompletionUp} :
    regularCauchyLocatedCompletionToEventFlow x =
      regularCauchyLocatedCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedCompletionFromEventFlow
          (regularCauchyLocatedCompletionToEventFlow x) =
        regularCauchyLocatedCompletionFromEventFlow
          (regularCauchyLocatedCompletionToEventFlow y) :=
    congrArg regularCauchyLocatedCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyLocatedCompletionUp,
      regularCauchyLocatedCompletionFields x =
        regularCauchyLocatedCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stream regular dyadic located completion realSeal transport replay provenance localName =>
      cases y with
      | mk stream' regular' dyadic' located' completion' realSeal' transport' replay'
          provenance' localName' =>
          cases hfields
          rfl

instance regularCauchyLocatedCompletionBHistCarrier :
    BHistCarrier RegularCauchyLocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedCompletionToEventFlow
  fromEventFlow := regularCauchyLocatedCompletionFromEventFlow

instance regularCauchyLocatedCompletionChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedCompletionFromEventFlow
        (regularCauchyLocatedCompletionToEventFlow x) = some x
    exact RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyLocatedCompletionFieldFaithful :
    FieldFaithful RegularCauchyLocatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLocatedCompletionFields
  field_faithful :=
    RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate RegularCauchyLocatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocatedCompletionChapterTasteGate

theorem RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyLocatedCompletionUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyLocatedCompletionUp) ∧
        (∀ x y : RegularCauchyLocatedCompletionUp,
          regularCauchyLocatedCompletionFields x =
            regularCauchyLocatedCompletionFields y -> x = y) ∧
          regularCauchyLocatedCompletionFields
              (RegularCauchyLocatedCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regularCauchyLocatedCompletionBHistCarrier⟩,
      ⟨regularCauchyLocatedCompletionChapterTasteGate⟩,
      RegularCauchyLocatedCompletionTasteGate_single_carrier_alignment_field_faithful,
      rfl⟩

end BEDC.Derived.RegularCauchyLocatedCompletionUp
