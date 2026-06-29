import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PreuniformityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PreuniformityUp : Type where
  | mk (source entourage base topology transport replay provenance localName : BHist) :
      PreuniformityUp
  deriving DecidableEq

def preuniformityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: preuniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: preuniformityEncodeBHist h

def preuniformityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (preuniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (preuniformityDecodeBHist tail)

private theorem preuniformityDecode_encode_bhist :
    ∀ h : BHist, preuniformityDecodeBHist (preuniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def preuniformityToEventFlow : PreuniformityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PreuniformityUp.mk source entourage base topology transport replay provenance localName =>
      [[BMark.b0],
        preuniformityEncodeBHist source,
        [BMark.b1, BMark.b0],
        preuniformityEncodeBHist entourage,
        [BMark.b1, BMark.b1, BMark.b0],
        preuniformityEncodeBHist base,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        preuniformityEncodeBHist topology,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        preuniformityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        preuniformityEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        preuniformityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        preuniformityEncodeBHist localName]

def preuniformityFromEventFlow : EventFlow → Option PreuniformityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | entourage :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | base :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | topology :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (PreuniformityUp.mk
                                                                          (preuniformityDecodeBHist source)
                                                                          (preuniformityDecodeBHist entourage)
                                                                          (preuniformityDecodeBHist base)
                                                                          (preuniformityDecodeBHist topology)
                                                                          (preuniformityDecodeBHist transport)
                                                                          (preuniformityDecodeBHist replay)
                                                                          (preuniformityDecodeBHist provenance)
                                                                          (preuniformityDecodeBHist localName))
                                                                  | _ :: _ => none

private theorem preuniformity_round_trip :
    ∀ x : PreuniformityUp,
      preuniformityFromEventFlow (preuniformityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source entourage base topology transport replay provenance localName =>
      change
        some
          (PreuniformityUp.mk
            (preuniformityDecodeBHist (preuniformityEncodeBHist source))
            (preuniformityDecodeBHist (preuniformityEncodeBHist entourage))
            (preuniformityDecodeBHist (preuniformityEncodeBHist base))
            (preuniformityDecodeBHist (preuniformityEncodeBHist topology))
            (preuniformityDecodeBHist (preuniformityEncodeBHist transport))
            (preuniformityDecodeBHist (preuniformityEncodeBHist replay))
            (preuniformityDecodeBHist (preuniformityEncodeBHist provenance))
            (preuniformityDecodeBHist (preuniformityEncodeBHist localName))) =
          some
            (PreuniformityUp.mk source entourage base topology transport replay provenance
              localName)
      rw [preuniformityDecode_encode_bhist source,
        preuniformityDecode_encode_bhist entourage,
        preuniformityDecode_encode_bhist base,
        preuniformityDecode_encode_bhist topology,
        preuniformityDecode_encode_bhist transport,
        preuniformityDecode_encode_bhist replay,
        preuniformityDecode_encode_bhist provenance,
        preuniformityDecode_encode_bhist localName]

private theorem preuniformityToEventFlow_injective {x y : PreuniformityUp} :
    preuniformityToEventFlow x = preuniformityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      preuniformityFromEventFlow (preuniformityToEventFlow x) =
        preuniformityFromEventFlow (preuniformityToEventFlow y) :=
    congrArg preuniformityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (preuniformity_round_trip x).symm
      (Eq.trans hread (preuniformity_round_trip y)))

instance preuniformityBHistCarrier : BHistCarrier PreuniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := preuniformityToEventFlow
  fromEventFlow := preuniformityFromEventFlow

instance preuniformityChapterTasteGate : ChapterTasteGate PreuniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change preuniformityFromEventFlow (preuniformityToEventFlow x) = some x
    exact preuniformity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (preuniformityToEventFlow_injective heq)

theorem PreuniformityTasteGate_single_carrier_alignment :
    (∀ h : BHist, preuniformityDecodeBHist (preuniformityEncodeBHist h) = h) ∧
      (∀ x : PreuniformityUp,
        preuniformityFromEventFlow (preuniformityToEventFlow x) = some x) ∧
        (∀ x y : PreuniformityUp,
          preuniformityToEventFlow x = preuniformityToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact preuniformityDecode_encode_bhist
  · constructor
    · exact preuniformity_round_trip
    · intro x y heq
      exact preuniformityToEventFlow_injective heq

end BEDC.Derived.PreuniformityUp
