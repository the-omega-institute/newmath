import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubspaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubspaceUp : Type where
  | mk :
      (readback windows tolerance subspace classifier realSeal transport replay provenance
        localName : BHist) →
        RegularCauchySubspaceUp
  deriving DecidableEq

def regularCauchySubspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubspaceEncodeBHist h

def regularCauchySubspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubspaceDecodeBHist tail)

private theorem regularCauchySubspace_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchySubspaceDecodeBHist (regularCauchySubspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchySubspace_mk_congr
    {readback readback' windows windows' tolerance tolerance' subspace subspace'
      classifier classifier' realSeal realSeal' transport transport' replay replay'
      provenance provenance' localName localName' : BHist}
    (hReadback : readback' = readback)
    (hWindows : windows' = windows)
    (hTolerance : tolerance' = tolerance)
    (hSubspace : subspace' = subspace)
    (hClassifier : classifier' = classifier)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RegularCauchySubspaceUp.mk readback' windows' tolerance' subspace' classifier'
        realSeal' transport' replay' provenance' localName' =
      RegularCauchySubspaceUp.mk readback windows tolerance subspace classifier realSeal
        transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hReadback
  cases hWindows
  cases hTolerance
  cases hSubspace
  cases hClassifier
  cases hRealSeal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def regularCauchySubspaceToEventFlow : RegularCauchySubspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubspaceUp.mk readback windows tolerance subspace classifier realSeal
      transport replay provenance localName =>
      [[BMark.b0],
        regularCauchySubspaceEncodeBHist readback,
        [BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist windows,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist subspace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchySubspaceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubspaceEncodeBHist localName]

def regularCauchySubspaceFromEventFlow : EventFlow → Option RegularCauchySubspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: readback :: _tag1 :: windows :: _tag2 :: tolerance :: _tag3 :: subspace ::
      _tag4 :: classifier :: _tag5 :: realSeal :: _tag6 :: transport :: _tag7 ::
      replay :: _tag8 :: provenance :: _tag9 :: localName :: [] =>
        some
          (RegularCauchySubspaceUp.mk
            (regularCauchySubspaceDecodeBHist readback)
            (regularCauchySubspaceDecodeBHist windows)
            (regularCauchySubspaceDecodeBHist tolerance)
            (regularCauchySubspaceDecodeBHist subspace)
            (regularCauchySubspaceDecodeBHist classifier)
            (regularCauchySubspaceDecodeBHist realSeal)
            (regularCauchySubspaceDecodeBHist transport)
            (regularCauchySubspaceDecodeBHist replay)
            (regularCauchySubspaceDecodeBHist provenance)
            (regularCauchySubspaceDecodeBHist localName))
  | _ => none

private theorem regularCauchySubspace_round_trip :
    ∀ x : RegularCauchySubspaceUp,
      regularCauchySubspaceFromEventFlow
        (regularCauchySubspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk readback windows tolerance subspace classifier realSeal transport replay provenance
      localName =>
      change
        some
          (RegularCauchySubspaceUp.mk
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist readback))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist windows))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist tolerance))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist subspace))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist classifier))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist realSeal))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist transport))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist replay))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist provenance))
            (regularCauchySubspaceDecodeBHist
              (regularCauchySubspaceEncodeBHist localName))) =
          some
            (RegularCauchySubspaceUp.mk readback windows tolerance subspace classifier
              realSeal transport replay provenance localName)
      exact
        congrArg some
          (regularCauchySubspace_mk_congr
            (regularCauchySubspace_decode_encode_bhist readback)
            (regularCauchySubspace_decode_encode_bhist windows)
            (regularCauchySubspace_decode_encode_bhist tolerance)
            (regularCauchySubspace_decode_encode_bhist subspace)
            (regularCauchySubspace_decode_encode_bhist classifier)
            (regularCauchySubspace_decode_encode_bhist realSeal)
            (regularCauchySubspace_decode_encode_bhist transport)
            (regularCauchySubspace_decode_encode_bhist replay)
            (regularCauchySubspace_decode_encode_bhist provenance)
            (regularCauchySubspace_decode_encode_bhist localName))

private theorem regularCauchySubspaceToEventFlow_injective
    {x y : RegularCauchySubspaceUp} :
    regularCauchySubspaceToEventFlow x = regularCauchySubspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubspaceFromEventFlow (regularCauchySubspaceToEventFlow x) =
        regularCauchySubspaceFromEventFlow (regularCauchySubspaceToEventFlow y) :=
    congrArg regularCauchySubspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubspace_round_trip x).symm
      (Eq.trans hread (regularCauchySubspace_round_trip y)))

instance regularCauchySubspaceBHistCarrier : BHistCarrier RegularCauchySubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubspaceToEventFlow
  fromEventFlow := regularCauchySubspaceFromEventFlow

instance regularCauchySubspaceChapterTasteGate :
    ChapterTasteGate RegularCauchySubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubspaceFromEventFlow
        (regularCauchySubspaceToEventFlow x) = some x
    exact regularCauchySubspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubspaceToEventFlow_injective heq)

theorem RegularCauchySubspaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchySubspaceDecodeBHist
      (regularCauchySubspaceEncodeBHist h) = h) ∧
      regularCauchySubspaceEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ readback windows tolerance subspace classifier realSeal transport replay provenance
            localName : BHist,
          regularCauchySubspaceToEventFlow
              (RegularCauchySubspaceUp.mk readback windows tolerance subspace classifier realSeal
                transport replay provenance localName) =
            [[BMark.b0],
              regularCauchySubspaceEncodeBHist readback,
              [BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist windows,
              [BMark.b1, BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist tolerance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist subspace,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist classifier,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist realSeal,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              regularCauchySubspaceEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist replay,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regularCauchySubspaceEncodeBHist localName]) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨regularCauchySubspace_decode_encode_bhist, rfl, by
    intro readback windows tolerance subspace classifier realSeal transport replay provenance
      localName
    rfl⟩

end BEDC.Derived.RegularCauchySubspaceUp
