import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedIntegralUp : Type where
  | mk
      (interval integrand approximation stepPrimitive compatibility realHandoff errorLedger
        transport replay provenance localName : BHist) :
      RegulatedIntegralUp
  deriving DecidableEq

def regulatedIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedIntegralEncodeBHist h

def regulatedIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedIntegralDecodeBHist tail)

private theorem regulatedIntegral_decode_encode_bhist :
    ∀ h : BHist, regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regulatedIntegralEncodeBHist_injective {h k : BHist} :
    regulatedIntegralEncodeBHist h = regulatedIntegralEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist h) =
        regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist k) :=
    congrArg regulatedIntegralDecodeBHist heq
  exact
    Eq.trans (regulatedIntegral_decode_encode_bhist h).symm
      (Eq.trans hdecode (regulatedIntegral_decode_encode_bhist k))

private theorem regulatedIntegral_mk_congr
    {interval interval' integrand integrand' approximation approximation'
      stepPrimitive stepPrimitive' compatibility compatibility' realHandoff realHandoff'
      errorLedger errorLedger' transport transport' replay replay' provenance provenance'
      localName localName' : BHist}
    (hInterval : interval' = interval)
    (hIntegrand : integrand' = integrand)
    (hApproximation : approximation' = approximation)
    (hStepPrimitive : stepPrimitive' = stepPrimitive)
    (hCompatibility : compatibility' = compatibility)
    (hRealHandoff : realHandoff' = realHandoff)
    (hErrorLedger : errorLedger' = errorLedger)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RegulatedIntegralUp.mk interval' integrand' approximation' stepPrimitive' compatibility'
        realHandoff' errorLedger' transport' replay' provenance' localName' =
      RegulatedIntegralUp.mk interval integrand approximation stepPrimitive compatibility
        realHandoff errorLedger transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hInterval
  cases hIntegrand
  cases hApproximation
  cases hStepPrimitive
  cases hCompatibility
  cases hRealHandoff
  cases hErrorLedger
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def regulatedIntegralToEventFlow : RegulatedIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedIntegralUp.mk interval integrand approximation stepPrimitive compatibility
      realHandoff errorLedger transport replay provenance localName =>
      [[BMark.b0],
        regulatedIntegralEncodeBHist interval,
        regulatedIntegralEncodeBHist integrand,
        regulatedIntegralEncodeBHist approximation,
        regulatedIntegralEncodeBHist stepPrimitive,
        regulatedIntegralEncodeBHist compatibility,
        regulatedIntegralEncodeBHist realHandoff,
        regulatedIntegralEncodeBHist errorLedger,
        regulatedIntegralEncodeBHist transport,
        regulatedIntegralEncodeBHist replay,
        regulatedIntegralEncodeBHist provenance,
        regulatedIntegralEncodeBHist localName]

def regulatedIntegralFromEventFlow : EventFlow → Option RegulatedIntegralUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest =>
      match rest with
      | [] => none
      | interval :: rest =>
          match rest with
          | [] => none
          | integrand :: rest =>
              match rest with
              | [] => none
              | approximation :: rest =>
                  match rest with
                  | [] => none
                  | stepPrimitive :: rest =>
                      match rest with
                      | [] => none
                      | compatibility :: rest =>
                          match rest with
                          | [] => none
                          | realHandoff :: rest =>
                              match rest with
                              | [] => none
                              | errorLedger :: rest =>
                                  match rest with
                                  | [] => none
                                  | transport :: rest =>
                                      match rest with
                                      | [] => none
                                      | replay :: rest =>
                                          match rest with
                                          | [] => none
                                          | provenance :: rest =>
                                              match rest with
                                              | [] => none
                                              | localName :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (RegulatedIntegralUp.mk
                                                          (regulatedIntegralDecodeBHist interval)
                                                          (regulatedIntegralDecodeBHist integrand)
                                                          (regulatedIntegralDecodeBHist approximation)
                                                          (regulatedIntegralDecodeBHist stepPrimitive)
                                                          (regulatedIntegralDecodeBHist compatibility)
                                                          (regulatedIntegralDecodeBHist realHandoff)
                                                          (regulatedIntegralDecodeBHist errorLedger)
                                                          (regulatedIntegralDecodeBHist transport)
                                                          (regulatedIntegralDecodeBHist replay)
                                                          (regulatedIntegralDecodeBHist provenance)
                                                          (regulatedIntegralDecodeBHist localName))
                                                  | _ :: _ => none

private theorem regulatedIntegral_round_trip :
    ∀ x : RegulatedIntegralUp,
      regulatedIntegralFromEventFlow (regulatedIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval integrand approximation stepPrimitive compatibility realHandoff errorLedger
      transport replay provenance localName =>
      change
        some
          (RegulatedIntegralUp.mk
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist interval))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist integrand))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist approximation))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist stepPrimitive))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist compatibility))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist realHandoff))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist errorLedger))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist transport))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist replay))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist provenance))
            (regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist localName))) =
          some
            (RegulatedIntegralUp.mk interval integrand approximation stepPrimitive compatibility
              realHandoff errorLedger transport replay provenance localName)
      exact
        congrArg some
          (regulatedIntegral_mk_congr
            (regulatedIntegral_decode_encode_bhist interval)
            (regulatedIntegral_decode_encode_bhist integrand)
            (regulatedIntegral_decode_encode_bhist approximation)
            (regulatedIntegral_decode_encode_bhist stepPrimitive)
            (regulatedIntegral_decode_encode_bhist compatibility)
            (regulatedIntegral_decode_encode_bhist realHandoff)
            (regulatedIntegral_decode_encode_bhist errorLedger)
            (regulatedIntegral_decode_encode_bhist transport)
            (regulatedIntegral_decode_encode_bhist replay)
            (regulatedIntegral_decode_encode_bhist provenance)
            (regulatedIntegral_decode_encode_bhist localName))

private theorem regulatedIntegralToEventFlow_injective {x y : RegulatedIntegralUp} :
    regulatedIntegralToEventFlow x = regulatedIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk interval integrand approximation stepPrimitive compatibility realHandoff errorLedger
      transport replay provenance localName =>
      cases y with
      | mk interval' integrand' approximation' stepPrimitive' compatibility' realHandoff'
          errorLedger' transport' replay' provenance' localName' =>
          injection heq with _tagEq tailEq0
          injection tailEq0 with intervalEq tailEq1
          injection tailEq1 with integrandEq tailEq2
          injection tailEq2 with approximationEq tailEq3
          injection tailEq3 with stepPrimitiveEq tailEq4
          injection tailEq4 with compatibilityEq tailEq5
          injection tailEq5 with realHandoffEq tailEq6
          injection tailEq6 with errorLedgerEq tailEq7
          injection tailEq7 with transportEq tailEq8
          injection tailEq8 with replayEq tailEq9
          injection tailEq9 with provenanceEq tailEq10
          injection tailEq10 with localNameEq _nilEq
          exact
            regulatedIntegral_mk_congr
              (regulatedIntegralEncodeBHist_injective intervalEq)
              (regulatedIntegralEncodeBHist_injective integrandEq)
              (regulatedIntegralEncodeBHist_injective approximationEq)
              (regulatedIntegralEncodeBHist_injective stepPrimitiveEq)
              (regulatedIntegralEncodeBHist_injective compatibilityEq)
              (regulatedIntegralEncodeBHist_injective realHandoffEq)
              (regulatedIntegralEncodeBHist_injective errorLedgerEq)
              (regulatedIntegralEncodeBHist_injective transportEq)
              (regulatedIntegralEncodeBHist_injective replayEq)
              (regulatedIntegralEncodeBHist_injective provenanceEq)
              (regulatedIntegralEncodeBHist_injective localNameEq)

instance regulatedIntegralBHistCarrier : BHistCarrier RegulatedIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedIntegralToEventFlow
  fromEventFlow := regulatedIntegralFromEventFlow

instance regulatedIntegralChapterTasteGate : ChapterTasteGate RegulatedIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedIntegralFromEventFlow (regulatedIntegralToEventFlow x) = some x
    exact regulatedIntegral_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regulatedIntegralToEventFlow_injective heq)

theorem RegulatedIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist, regulatedIntegralDecodeBHist (regulatedIntegralEncodeBHist h) = h) ∧
      (∀ x : RegulatedIntegralUp,
        regulatedIntegralFromEventFlow (regulatedIntegralToEventFlow x) = some x) ∧
        (∀ x y : RegulatedIntegralUp,
          regulatedIntegralToEventFlow x = regulatedIntegralToEventFlow y → x = y) ∧
          regulatedIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact regulatedIntegral_decode_encode_bhist h
  · constructor
    · intro x
      cases x with
      | mk interval integrand approximation stepPrimitive compatibility realHandoff errorLedger
          transport replay provenance localName =>
          exact
            congrArg some
              (regulatedIntegral_mk_congr
                (regulatedIntegral_decode_encode_bhist interval)
                (regulatedIntegral_decode_encode_bhist integrand)
                (regulatedIntegral_decode_encode_bhist approximation)
                (regulatedIntegral_decode_encode_bhist stepPrimitive)
                (regulatedIntegral_decode_encode_bhist compatibility)
                (regulatedIntegral_decode_encode_bhist realHandoff)
                (regulatedIntegral_decode_encode_bhist errorLedger)
                (regulatedIntegral_decode_encode_bhist transport)
                (regulatedIntegral_decode_encode_bhist replay)
                (regulatedIntegral_decode_encode_bhist provenance)
                (regulatedIntegral_decode_encode_bhist localName))
    · constructor
      · intro x y heq
        exact regulatedIntegralToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegulatedIntegralUp
