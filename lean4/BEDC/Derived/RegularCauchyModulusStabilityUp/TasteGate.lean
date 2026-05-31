import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusStabilityUp : Type where
  | mk
      (sourceA sourceB modulus tailLedger windowA windowB dyadicA dyadicB readbackA
        readbackB sealA sealB transport replay provenance localName : BHist) :
      RegularCauchyModulusStabilityUp
  deriving DecidableEq

def regularCauchyModulusStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusStabilityEncodeBHist h

def regularCauchyModulusStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusStabilityDecodeBHist tail)

private theorem regularCauchyModulusStabilityDecode_encode :
    ∀ h : BHist,
      regularCauchyModulusStabilityDecodeBHist
          (regularCauchyModulusStabilityEncodeBHist h) =
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

def regularCauchyModulusStabilityToEventFlow :
    RegularCauchyModulusStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusStabilityUp.mk sourceA sourceB modulus tailLedger windowA windowB
      dyadicA dyadicB readbackA readbackB sealA sealB transport replay provenance localName =>
      [regularCauchyModulusStabilityEncodeBHist sourceA,
        regularCauchyModulusStabilityEncodeBHist sourceB,
        regularCauchyModulusStabilityEncodeBHist modulus,
        regularCauchyModulusStabilityEncodeBHist tailLedger,
        regularCauchyModulusStabilityEncodeBHist windowA,
        regularCauchyModulusStabilityEncodeBHist windowB,
        regularCauchyModulusStabilityEncodeBHist dyadicA,
        regularCauchyModulusStabilityEncodeBHist dyadicB,
        regularCauchyModulusStabilityEncodeBHist readbackA,
        regularCauchyModulusStabilityEncodeBHist readbackB,
        regularCauchyModulusStabilityEncodeBHist sealA,
        regularCauchyModulusStabilityEncodeBHist sealB,
        regularCauchyModulusStabilityEncodeBHist transport,
        regularCauchyModulusStabilityEncodeBHist replay,
        regularCauchyModulusStabilityEncodeBHist provenance,
        regularCauchyModulusStabilityEncodeBHist localName]

def regularCauchyModulusStabilityFromEventFlow :
    EventFlow → Option RegularCauchyModulusStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceA :: restSourceB =>
      match restSourceB with
      | [] => none
      | sourceB :: restModulus =>
          match restModulus with
          | [] => none
          | modulus :: restTailLedger =>
              match restTailLedger with
              | [] => none
              | tailLedger :: restWindowA =>
                  match restWindowA with
                  | [] => none
                  | windowA :: restWindowB =>
                      match restWindowB with
                      | [] => none
                      | windowB :: restDyadicA =>
                          match restDyadicA with
                          | [] => none
                          | dyadicA :: restDyadicB =>
                              match restDyadicB with
                              | [] => none
                              | dyadicB :: restReadbackA =>
                                  match restReadbackA with
                                  | [] => none
                                  | readbackA :: restReadbackB =>
                                      match restReadbackB with
                                      | [] => none
                                      | readbackB :: restSealA =>
                                          match restSealA with
                                          | [] => none
                                          | sealA :: restSealB =>
                                              match restSealB with
                                              | [] => none
                                              | sealB :: restTransport =>
                                                  match restTransport with
                                                  | [] => none
                                                  | transport :: restReplay =>
                                                      match restReplay with
                                                      | [] => none
                                                      | replay :: restProvenance =>
                                                          match restProvenance with
                                                          | [] => none
                                                          | provenance :: restLocalName =>
                                                              match restLocalName with
                                                              | [] => none
                                                              | localName :: rest =>
                                                                  match rest with
                                                                  | [] =>
                                                                      some
                                                                        (RegularCauchyModulusStabilityUp.mk
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            sourceA)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            sourceB)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            modulus)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            tailLedger)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            windowA)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            windowB)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            dyadicA)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            dyadicB)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            readbackA)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            readbackB)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            sealA)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            sealB)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            transport)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            replay)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            provenance)
                                                                          (regularCauchyModulusStabilityDecodeBHist
                                                                            localName))
                                                                  | _ :: _ => none

private theorem regularCauchyModulusStability_round_trip :
    ∀ x : RegularCauchyModulusStabilityUp,
      regularCauchyModulusStabilityFromEventFlow
          (regularCauchyModulusStabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceA sourceB modulus tailLedger windowA windowB dyadicA dyadicB readbackA
      readbackB sealA sealB transport replay provenance localName =>
      change
        some
            (RegularCauchyModulusStabilityUp.mk
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist sourceA))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist sourceB))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist modulus))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist tailLedger))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist windowA))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist windowB))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist dyadicA))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist dyadicB))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist readbackA))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist readbackB))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist sealA))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist sealB))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist transport))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist replay))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist provenance))
              (regularCauchyModulusStabilityDecodeBHist
                (regularCauchyModulusStabilityEncodeBHist localName))) =
          some
            (RegularCauchyModulusStabilityUp.mk sourceA sourceB modulus tailLedger windowA
              windowB dyadicA dyadicB readbackA readbackB sealA sealB transport replay
              provenance localName)
      rw [regularCauchyModulusStabilityDecode_encode sourceA,
        regularCauchyModulusStabilityDecode_encode sourceB,
        regularCauchyModulusStabilityDecode_encode modulus,
        regularCauchyModulusStabilityDecode_encode tailLedger,
        regularCauchyModulusStabilityDecode_encode windowA,
        regularCauchyModulusStabilityDecode_encode windowB,
        regularCauchyModulusStabilityDecode_encode dyadicA,
        regularCauchyModulusStabilityDecode_encode dyadicB,
        regularCauchyModulusStabilityDecode_encode readbackA,
        regularCauchyModulusStabilityDecode_encode readbackB,
        regularCauchyModulusStabilityDecode_encode sealA,
        regularCauchyModulusStabilityDecode_encode sealB,
        regularCauchyModulusStabilityDecode_encode transport,
        regularCauchyModulusStabilityDecode_encode replay,
        regularCauchyModulusStabilityDecode_encode provenance,
        regularCauchyModulusStabilityDecode_encode localName]

private theorem regularCauchyModulusStabilityToEventFlow_injective
    {x y : RegularCauchyModulusStabilityUp} :
    regularCauchyModulusStabilityToEventFlow x =
        regularCauchyModulusStabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusStabilityFromEventFlow
          (regularCauchyModulusStabilityToEventFlow x) =
        regularCauchyModulusStabilityFromEventFlow
          (regularCauchyModulusStabilityToEventFlow y) :=
    congrArg regularCauchyModulusStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyModulusStability_round_trip x).symm
      (Eq.trans hread (regularCauchyModulusStability_round_trip y)))

private def regularCauchyModulusStabilityBHistCarrierDef :
    BHistCarrier RegularCauchyModulusStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusStabilityToEventFlow
  fromEventFlow := regularCauchyModulusStabilityFromEventFlow

instance regularCauchyModulusStabilityBHistCarrier :
    BHistCarrier RegularCauchyModulusStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyModulusStabilityBHistCarrierDef

private def regularCauchyModulusStabilityChapterTasteGateDef :
    ChapterTasteGate RegularCauchyModulusStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusStabilityFromEventFlow
          (regularCauchyModulusStabilityToEventFlow x) =
        some x
    exact regularCauchyModulusStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyModulusStabilityToEventFlow_injective heq)

instance regularCauchyModulusStabilityChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyModulusStabilityChapterTasteGateDef

theorem RegularCauchyModulusStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyModulusStabilityDecodeBHist
          (regularCauchyModulusStabilityEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyModulusStabilityUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyModulusStabilityUp) ∧
          regularCauchyModulusStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyModulusStabilityDecode_encode
  · constructor
    · exact ⟨regularCauchyModulusStabilityBHistCarrierDef⟩
    · constructor
      · exact ⟨regularCauchyModulusStabilityChapterTasteGateDef⟩
      · rfl

end BEDC.Derived.RegularCauchyModulusStabilityUp
