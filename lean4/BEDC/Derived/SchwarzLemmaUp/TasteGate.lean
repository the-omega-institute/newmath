import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwarzLemmaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwarzLemmaUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (holomorphic disk zeroFixing unitBound modulus route transport provenance localName :
        BHist) ->
        SchwarzLemmaUp
  deriving DecidableEq

def schwarzLemmaEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwarzLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwarzLemmaEncodeBHist h

def schwarzLemmaDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwarzLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwarzLemmaDecodeBHist tail)

private theorem schwarzLemmaDecodeEncode :
    ∀ h : BHist, schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def schwarzLemmaFields : SchwarzLemmaUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwarzLemmaUp.mk holomorphic disk zeroFixing unitBound modulus route transport provenance
      localName =>
      [holomorphic, disk, zeroFixing, unitBound, modulus, route, transport, provenance,
        localName]

def schwarzLemmaToEventFlow : SchwarzLemmaUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (schwarzLemmaFields x).map schwarzLemmaEncodeBHist

def schwarzLemmaFromEventFlow : EventFlow -> Option SchwarzLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | [holomorphic, disk, zeroFixing, unitBound, modulus, route, transport, provenance,
      localName] =>
      some
        (SchwarzLemmaUp.mk
          (schwarzLemmaDecodeBHist holomorphic)
          (schwarzLemmaDecodeBHist disk)
          (schwarzLemmaDecodeBHist zeroFixing)
          (schwarzLemmaDecodeBHist unitBound)
          (schwarzLemmaDecodeBHist modulus)
          (schwarzLemmaDecodeBHist route)
          (schwarzLemmaDecodeBHist transport)
          (schwarzLemmaDecodeBHist provenance)
          (schwarzLemmaDecodeBHist localName))
  | _ => none

private theorem schwarzLemmaRoundTrip (x : SchwarzLemmaUp) :
    schwarzLemmaFromEventFlow (schwarzLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk holomorphic disk zeroFixing unitBound modulus route transport provenance localName =>
      change
        some
          (SchwarzLemmaUp.mk
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist holomorphic))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist disk))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist zeroFixing))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist unitBound))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist modulus))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist route))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist transport))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist provenance))
            (schwarzLemmaDecodeBHist (schwarzLemmaEncodeBHist localName))) =
          some
            (SchwarzLemmaUp.mk holomorphic disk zeroFixing unitBound modulus route transport
              provenance localName)
      rw [schwarzLemmaDecodeEncode holomorphic, schwarzLemmaDecodeEncode disk,
        schwarzLemmaDecodeEncode zeroFixing, schwarzLemmaDecodeEncode unitBound,
        schwarzLemmaDecodeEncode modulus, schwarzLemmaDecodeEncode route,
        schwarzLemmaDecodeEncode transport, schwarzLemmaDecodeEncode provenance,
        schwarzLemmaDecodeEncode localName]

private theorem schwarzLemmaToEventFlow_injective {x y : SchwarzLemmaUp} :
    schwarzLemmaToEventFlow x = schwarzLemmaToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwarzLemmaFromEventFlow (schwarzLemmaToEventFlow x) =
        schwarzLemmaFromEventFlow (schwarzLemmaToEventFlow y) :=
    congrArg schwarzLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schwarzLemmaRoundTrip x).symm
      (Eq.trans hread (schwarzLemmaRoundTrip y)))

instance schwarzLemmaBHistCarrier : BHistCarrier SchwarzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwarzLemmaToEventFlow
  fromEventFlow := schwarzLemmaFromEventFlow

instance schwarzLemmaChapterTasteGate : ChapterTasteGate SchwarzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwarzLemmaFromEventFlow (schwarzLemmaToEventFlow x) = some x
    exact schwarzLemmaRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schwarzLemmaToEventFlow_injective heq)

theorem SchwarzLemmaTasteGate_single_carrier_alignment :
    schwarzLemmaEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      schwarzLemmaEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        schwarzLemmaEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

end BEDC.Derived.SchwarzLemmaUp.TasteGate
