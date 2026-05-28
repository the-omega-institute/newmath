import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteVitaliCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteVitaliCoverUp : Type where
  | mk
      (locatedIntervals dyadicRadii selectedSubfamily shadowCoverage transport replay
        provenance localName : BHist) :
      FiniteVitaliCoverUp
  deriving DecidableEq

def finiteVitaliCoverTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def finiteVitaliCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteVitaliCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteVitaliCoverEncodeBHist h

def finiteVitaliCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteVitaliCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteVitaliCoverDecodeBHist tail)

private theorem finiteVitaliCover_decode_encode_bhist :
    ∀ h : BHist, finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteVitaliCoverToEventFlow : FiniteVitaliCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteVitaliCoverUp.mk locatedIntervals dyadicRadii selectedSubfamily shadowCoverage
      transport replay provenance localName =>
      [finiteVitaliCoverTag,
        finiteVitaliCoverEncodeBHist locatedIntervals,
        finiteVitaliCoverEncodeBHist dyadicRadii,
        finiteVitaliCoverEncodeBHist selectedSubfamily,
        finiteVitaliCoverEncodeBHist shadowCoverage,
        finiteVitaliCoverEncodeBHist transport,
        finiteVitaliCoverEncodeBHist replay,
        finiteVitaliCoverEncodeBHist provenance,
        finiteVitaliCoverEncodeBHist localName]

def finiteVitaliCoverFromEventFlow : EventFlow → Option FiniteVitaliCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | locatedIntervals :: rest1 =>
          match rest1 with
          | [] => none
          | dyadicRadii :: rest2 =>
              match rest2 with
              | [] => none
              | selectedSubfamily :: rest3 =>
                  match rest3 with
                  | [] => none
                  | shadowCoverage :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (FiniteVitaliCoverUp.mk
                                              (finiteVitaliCoverDecodeBHist locatedIntervals)
                                              (finiteVitaliCoverDecodeBHist dyadicRadii)
                                              (finiteVitaliCoverDecodeBHist selectedSubfamily)
                                              (finiteVitaliCoverDecodeBHist shadowCoverage)
                                              (finiteVitaliCoverDecodeBHist transport)
                                              (finiteVitaliCoverDecodeBHist replay)
                                              (finiteVitaliCoverDecodeBHist provenance)
                                              (finiteVitaliCoverDecodeBHist localName))
                                      | _ :: _ => none

private theorem finiteVitaliCover_round_trip :
    ∀ x : FiniteVitaliCoverUp,
      finiteVitaliCoverFromEventFlow (finiteVitaliCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk locatedIntervals dyadicRadii selectedSubfamily shadowCoverage transport replay
      provenance localName =>
      change
        some
            (FiniteVitaliCoverUp.mk
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist locatedIntervals))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist dyadicRadii))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist selectedSubfamily))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist shadowCoverage))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist transport))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist replay))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist provenance))
              (finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist localName))) =
          some
            (FiniteVitaliCoverUp.mk locatedIntervals dyadicRadii selectedSubfamily
              shadowCoverage transport replay provenance localName)
      rw [finiteVitaliCover_decode_encode_bhist locatedIntervals,
        finiteVitaliCover_decode_encode_bhist dyadicRadii,
        finiteVitaliCover_decode_encode_bhist selectedSubfamily,
        finiteVitaliCover_decode_encode_bhist shadowCoverage,
        finiteVitaliCover_decode_encode_bhist transport,
        finiteVitaliCover_decode_encode_bhist replay,
        finiteVitaliCover_decode_encode_bhist provenance,
        finiteVitaliCover_decode_encode_bhist localName]

private theorem finiteVitaliCoverToEventFlow_injective {x y : FiniteVitaliCoverUp} :
    finiteVitaliCoverToEventFlow x = finiteVitaliCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteVitaliCoverFromEventFlow (finiteVitaliCoverToEventFlow x) =
        finiteVitaliCoverFromEventFlow (finiteVitaliCoverToEventFlow y) :=
    congrArg finiteVitaliCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteVitaliCover_round_trip x).symm
      (Eq.trans hread (finiteVitaliCover_round_trip y)))

instance finiteVitaliCoverBHistCarrier : BHistCarrier FiniteVitaliCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteVitaliCoverToEventFlow
  fromEventFlow := finiteVitaliCoverFromEventFlow

instance finiteVitaliCoverChapterTasteGate : ChapterTasteGate FiniteVitaliCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteVitaliCoverFromEventFlow (finiteVitaliCoverToEventFlow x) = some x
    exact finiteVitaliCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteVitaliCoverToEventFlow_injective heq)

theorem FiniteVitaliCoverTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteVitaliCoverUp) ∧
      Nonempty (ChapterTasteGate FiniteVitaliCoverUp) ∧
      (∀ h : BHist, finiteVitaliCoverDecodeBHist (finiteVitaliCoverEncodeBHist h) = h) ∧
        finiteVitaliCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨finiteVitaliCoverBHistCarrier⟩
  · constructor
    · exact ⟨finiteVitaliCoverChapterTasteGate⟩
    · constructor
      · exact finiteVitaliCover_decode_encode_bhist
      · rfl

end BEDC.Derived.FiniteVitaliCoverUp
