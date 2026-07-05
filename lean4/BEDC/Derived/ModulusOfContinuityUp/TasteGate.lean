import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusOfContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusOfContinuityUp : Type where
  | mk (source target tolerance precision pointwise uniform transport replay provenance
      localName : BHist) : ModulusOfContinuityUp
  deriving DecidableEq

def modulusOfContinuityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusOfContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusOfContinuityEncodeBHist h

def modulusOfContinuityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusOfContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusOfContinuityDecodeBHist tail)

private theorem modulusOfContinuityDecode_encode_bhist :
    forall h : BHist,
      modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusOfContinuityFields : ModulusOfContinuityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfContinuityUp.mk source target tolerance precision pointwise uniform transport
      replay provenance localName =>
      [source, target, tolerance, precision, pointwise, uniform, transport, replay,
        provenance, localName]

def modulusOfContinuityToEventFlow : ModulusOfContinuityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (modulusOfContinuityFields x).map modulusOfContinuityEncodeBHist

def modulusOfContinuityFromEventFlow : EventFlow -> Option ModulusOfContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | tolerance :: rest2 =>
              match rest2 with
              | [] => none
              | precision :: rest3 =>
                  match rest3 with
                  | [] => none
                  | pointwise :: rest4 =>
                      match rest4 with
                      | [] => none
                      | uniform :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ModulusOfContinuityUp.mk
                                                  (modulusOfContinuityDecodeBHist source)
                                                  (modulusOfContinuityDecodeBHist target)
                                                  (modulusOfContinuityDecodeBHist tolerance)
                                                  (modulusOfContinuityDecodeBHist precision)
                                                  (modulusOfContinuityDecodeBHist pointwise)
                                                  (modulusOfContinuityDecodeBHist uniform)
                                                  (modulusOfContinuityDecodeBHist transport)
                                                  (modulusOfContinuityDecodeBHist replay)
                                                  (modulusOfContinuityDecodeBHist provenance)
                                                  (modulusOfContinuityDecodeBHist localName))
                                          | _ :: _ => none

private theorem modulusOfContinuity_round_trip :
    forall x : ModulusOfContinuityUp,
      modulusOfContinuityFromEventFlow (modulusOfContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target tolerance precision pointwise uniform transport replay provenance
      localName =>
      change
        some
          (ModulusOfContinuityUp.mk
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist source))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist target))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist tolerance))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist precision))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist pointwise))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist uniform))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist transport))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist replay))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist provenance))
            (modulusOfContinuityDecodeBHist (modulusOfContinuityEncodeBHist localName))) =
          some
            (ModulusOfContinuityUp.mk source target tolerance precision pointwise uniform
              transport replay provenance localName)
      rw [modulusOfContinuityDecode_encode_bhist source,
        modulusOfContinuityDecode_encode_bhist target,
        modulusOfContinuityDecode_encode_bhist tolerance,
        modulusOfContinuityDecode_encode_bhist precision,
        modulusOfContinuityDecode_encode_bhist pointwise,
        modulusOfContinuityDecode_encode_bhist uniform,
        modulusOfContinuityDecode_encode_bhist transport,
        modulusOfContinuityDecode_encode_bhist replay,
        modulusOfContinuityDecode_encode_bhist provenance,
        modulusOfContinuityDecode_encode_bhist localName]

private theorem modulusOfContinuityToEventFlow_injective {x y : ModulusOfContinuityUp} :
    modulusOfContinuityToEventFlow x = modulusOfContinuityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusOfContinuityFromEventFlow (modulusOfContinuityToEventFlow x) =
        modulusOfContinuityFromEventFlow (modulusOfContinuityToEventFlow y) :=
    congrArg modulusOfContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modulusOfContinuity_round_trip x).symm
      (Eq.trans hread (modulusOfContinuity_round_trip y)))

instance modulusOfContinuityBHistCarrier : BHistCarrier ModulusOfContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusOfContinuityToEventFlow
  fromEventFlow := modulusOfContinuityFromEventFlow

instance modulusOfContinuityChapterTasteGate :
    ChapterTasteGate ModulusOfContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modulusOfContinuityFromEventFlow (modulusOfContinuityToEventFlow x) = some x
    exact modulusOfContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modulusOfContinuityToEventFlow_injective heq)

namespace TasteGate

theorem ModulusOfContinuityTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ModulusOfContinuityUp) ∧
      Nonempty (ChapterTasteGate ModulusOfContinuityUp) ∧
        modulusOfContinuityEncodeBHist BHist.Empty = [] ∧
          modulusOfContinuityDecodeBHist [BMark.b0] = BHist.e0 BHist.Empty ∧
            (forall x : ModulusOfContinuityUp,
              modulusOfContinuityFromEventFlow (modulusOfContinuityToEventFlow x) =
                some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨⟨modulusOfContinuityBHistCarrier⟩,
      ⟨modulusOfContinuityChapterTasteGate⟩, rfl, rfl, modulusOfContinuity_round_trip⟩

end TasteGate

end BEDC.Derived.ModulusOfContinuityUp
