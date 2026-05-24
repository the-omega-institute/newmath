import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusRealizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusRealizerUp : Type where
  | mk
      (request threshold window tolerance readback sealRow transport replay provenance
        localName : BHist) :
      RegularCauchyModulusRealizerUp
  deriving DecidableEq

def regularCauchyModulusRealizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusRealizerEncodeBHist h

def regularCauchyModulusRealizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusRealizerDecodeBHist tail)

private theorem regularCauchyModulusRealizerDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyModulusRealizerDecodeBHist
          (regularCauchyModulusRealizerEncodeBHist h) =
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

def regularCauchyModulusRealizerFields :
    RegularCauchyModulusRealizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusRealizerUp.mk request threshold window tolerance readback sealRow
      transport replay provenance localName =>
      [request, threshold, window, tolerance, readback, sealRow, transport, replay,
        provenance, localName]

def regularCauchyModulusRealizerToEventFlow :
    RegularCauchyModulusRealizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusRealizerUp.mk request threshold window tolerance readback sealRow
      transport replay provenance localName =>
      [[BMark.b0],
        regularCauchyModulusRealizerEncodeBHist request,
        [BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist threshold,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyModulusRealizerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusRealizerEncodeBHist localName]

def regularCauchyModulusRealizerFromEventFlow :
    EventFlow → Option RegularCauchyModulusRealizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagRequest :: restRequest =>
      match restRequest with
      | [] => none
      | request :: restThresholdTag =>
          match restThresholdTag with
          | [] => none
          | _tagThreshold :: restThreshold =>
              match restThreshold with
              | [] => none
              | threshold :: restWindowTag =>
                  match restWindowTag with
                  | [] => none
                  | _tagWindow :: restWindow =>
                      match restWindow with
                      | [] => none
                      | window :: restToleranceTag =>
                          match restToleranceTag with
                          | [] => none
                          | _tagTolerance :: restTolerance =>
                              match restTolerance with
                              | [] => none
                              | tolerance :: restReadbackTag =>
                                  match restReadbackTag with
                                  | [] => none
                                  | _tagReadback :: restReadback =>
                                      match restReadback with
                                      | [] => none
                                      | readback :: restSealTag =>
                                          match restSealTag with
                                          | [] => none
                                          | _tagSeal :: restSeal =>
                                              match restSeal with
                                              | [] => none
                                              | sealRow :: restTransportTag =>
                                                  match restTransportTag with
                                                  | [] => none
                                                  | _tagTransport :: restTransport =>
                                                      match restTransport with
                                                      | [] => none
                                                      | transport :: restReplayTag =>
                                                          match restReplayTag with
                                                          | [] => none
                                                          | _tagReplay :: restReplay =>
                                                              match restReplay with
                                                              | [] => none
                                                              | replay :: restProvenanceTag =>
                                                                  match restProvenanceTag with
                                                                  | [] => none
                                                                  | _tagProvenance ::
                                                                      restProvenance =>
                                                                      match restProvenance with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          restLocalNameTag =>
                                                                          match
                                                                            restLocalNameTag
                                                                          with
                                                                          | [] => none
                                                                          | _tagLocalName ::
                                                                              restLocalName =>
                                                                              match
                                                                                restLocalName
                                                                              with
                                                                              | [] => none
                                                                              | localName :: rest =>
                                                                                  match rest with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RegularCauchyModulusRealizerUp.mk
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            request)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            threshold)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            window)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            tolerance)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            readback)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            sealRow)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            transport)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            replay)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            provenance)
                                                                                          (regularCauchyModulusRealizerDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ => none

private theorem regularCauchyModulusRealizer_round_trip :
    ∀ x : RegularCauchyModulusRealizerUp,
      regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request threshold window tolerance readback sealRow transport replay provenance
      localName =>
      change
        some
            (RegularCauchyModulusRealizerUp.mk
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist request))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist threshold))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist window))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist tolerance))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist readback))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist sealRow))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist transport))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist replay))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist provenance))
              (regularCauchyModulusRealizerDecodeBHist
                (regularCauchyModulusRealizerEncodeBHist localName))) =
          some
            (RegularCauchyModulusRealizerUp.mk request threshold window tolerance readback
              sealRow transport replay provenance localName)
      rw [regularCauchyModulusRealizerDecode_encode_bhist request,
        regularCauchyModulusRealizerDecode_encode_bhist threshold,
        regularCauchyModulusRealizerDecode_encode_bhist window,
        regularCauchyModulusRealizerDecode_encode_bhist tolerance,
        regularCauchyModulusRealizerDecode_encode_bhist readback,
        regularCauchyModulusRealizerDecode_encode_bhist sealRow,
        regularCauchyModulusRealizerDecode_encode_bhist transport,
        regularCauchyModulusRealizerDecode_encode_bhist replay,
        regularCauchyModulusRealizerDecode_encode_bhist provenance,
        regularCauchyModulusRealizerDecode_encode_bhist localName]

private theorem regularCauchyModulusRealizerToEventFlow_injective
    {x y : RegularCauchyModulusRealizerUp} :
    regularCauchyModulusRealizerToEventFlow x =
        regularCauchyModulusRealizerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow x) =
        regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow y) :=
    congrArg regularCauchyModulusRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyModulusRealizer_round_trip x).symm
      (Eq.trans hread (regularCauchyModulusRealizer_round_trip y)))

instance regularCauchyModulusRealizerBHistCarrier :
    BHistCarrier RegularCauchyModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusRealizerToEventFlow
  fromEventFlow := regularCauchyModulusRealizerFromEventFlow

instance regularCauchyModulusRealizerChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow x) =
        some x
    exact regularCauchyModulusRealizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyModulusRealizerToEventFlow_injective heq)

theorem RegularCauchyModulusRealizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyModulusRealizerDecodeBHist
            (regularCauchyModulusRealizerEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyModulusRealizerUp,
        regularCauchyModulusRealizerFromEventFlow
            (regularCauchyModulusRealizerToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyModulusRealizerUp,
          regularCauchyModulusRealizerToEventFlow x =
              regularCauchyModulusRealizerToEventFlow y →
            x = y) ∧
          regularCauchyModulusRealizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyModulusRealizerDecode_encode_bhist,
      regularCauchyModulusRealizer_round_trip,
      (fun _ _ heq => regularCauchyModulusRealizerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyModulusRealizerUp
