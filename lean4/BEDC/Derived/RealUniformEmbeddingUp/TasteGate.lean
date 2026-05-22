import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformEmbeddingUp : Type where
  | mk
      (source windows dyadic readback sealRow uniformRow transport route provenance
        localCert : BHist) :
      RealUniformEmbeddingUp
  deriving DecidableEq

def realUniformEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEmbeddingEncodeBHist h

def realUniformEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEmbeddingDecodeBHist tail)

private theorem realUniformEmbedding_decode_encode_bhist :
    ∀ h : BHist,
      realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realUniformEmbeddingFields : RealUniformEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEmbeddingUp.mk source windows dyadic readback sealRow uniformRow transport
      route provenance localCert =>
      [source, windows, dyadic, readback, sealRow, uniformRow, transport, route, provenance,
        localCert]

def realUniformEmbeddingToEventFlow : RealUniformEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEmbeddingUp.mk source windows dyadic readback sealRow uniformRow transport
      route provenance localCert =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        realUniformEmbeddingEncodeBHist source,
        realUniformEmbeddingEncodeBHist windows,
        realUniformEmbeddingEncodeBHist dyadic,
        realUniformEmbeddingEncodeBHist readback,
        realUniformEmbeddingEncodeBHist sealRow,
        realUniformEmbeddingEncodeBHist uniformRow,
        realUniformEmbeddingEncodeBHist transport,
        realUniformEmbeddingEncodeBHist route,
        realUniformEmbeddingEncodeBHist provenance,
        realUniformEmbeddingEncodeBHist localCert]

def realUniformEmbeddingFromEventFlow :
    EventFlow → Option RealUniformEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b1, BMark.b1, BMark.b0, BMark.b1], source, windows, dyadic, readback,
      sealRow, uniformRow, transport, route, provenance, localCert] =>
      some
        (RealUniformEmbeddingUp.mk
          (realUniformEmbeddingDecodeBHist source)
          (realUniformEmbeddingDecodeBHist windows)
          (realUniformEmbeddingDecodeBHist dyadic)
          (realUniformEmbeddingDecodeBHist readback)
          (realUniformEmbeddingDecodeBHist sealRow)
          (realUniformEmbeddingDecodeBHist uniformRow)
          (realUniformEmbeddingDecodeBHist transport)
          (realUniformEmbeddingDecodeBHist route)
          (realUniformEmbeddingDecodeBHist provenance)
          (realUniformEmbeddingDecodeBHist localCert))
  | _ => none

private theorem realUniformEmbedding_round_trip :
    ∀ x : RealUniformEmbeddingUp,
      realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source windows dyadic readback sealRow uniformRow transport route provenance
      localCert =>
      change
        some
          (RealUniformEmbeddingUp.mk
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist source))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist windows))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist dyadic))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist readback))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist sealRow))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist uniformRow))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist transport))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist route))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist provenance))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist localCert))) =
          some
            (RealUniformEmbeddingUp.mk source windows dyadic readback sealRow uniformRow
              transport route provenance localCert)
      rw [realUniformEmbedding_decode_encode_bhist source,
        realUniformEmbedding_decode_encode_bhist windows,
        realUniformEmbedding_decode_encode_bhist dyadic,
        realUniformEmbedding_decode_encode_bhist readback,
        realUniformEmbedding_decode_encode_bhist sealRow,
        realUniformEmbedding_decode_encode_bhist uniformRow,
        realUniformEmbedding_decode_encode_bhist transport,
        realUniformEmbedding_decode_encode_bhist route,
        realUniformEmbedding_decode_encode_bhist provenance,
        realUniformEmbedding_decode_encode_bhist localCert]

private theorem realUniformEmbeddingToEventFlow_injective
    {x y : RealUniformEmbeddingUp} :
    realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) =
        realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow y) :=
    congrArg realUniformEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realUniformEmbedding_round_trip x).symm
      (Eq.trans hread (realUniformEmbedding_round_trip y)))

instance realUniformEmbeddingBHistCarrier :
    BHistCarrier RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEmbeddingToEventFlow
  fromEventFlow := realUniformEmbeddingFromEventFlow

instance realUniformEmbeddingChapterTasteGate :
    ChapterTasteGate RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x
    exact realUniformEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realUniformEmbeddingToEventFlow_injective heq)

instance realUniformEmbeddingNontrivial :
    Nontrivial RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformEmbeddingChapterTasteGate

theorem RealUniformEmbeddingUpTasteGate_single_carrier_alignment :
    forall source windows dyadic readback sealRow uniformRow transport route provenance
      localCert : BHist,
      realUniformEmbeddingToEventFlow
          (RealUniformEmbeddingUp.mk source windows dyadic readback sealRow uniformRow
            transport route provenance localCert) =
        [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
          realUniformEmbeddingEncodeBHist source,
          realUniformEmbeddingEncodeBHist windows,
          realUniformEmbeddingEncodeBHist dyadic,
          realUniformEmbeddingEncodeBHist readback,
          realUniformEmbeddingEncodeBHist sealRow,
          realUniformEmbeddingEncodeBHist uniformRow,
          realUniformEmbeddingEncodeBHist transport,
          realUniformEmbeddingEncodeBHist route,
          realUniformEmbeddingEncodeBHist provenance,
          realUniformEmbeddingEncodeBHist localCert] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro source windows dyadic readback sealRow uniformRow transport route provenance localCert
  rfl

end BEDC.Derived.RealUniformEmbeddingUp
