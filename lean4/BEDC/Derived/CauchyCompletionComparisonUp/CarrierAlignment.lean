import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.CauchyCompletionComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive CauchyCompletionComparisonUp : Type where
  | mk
      (unit universal functorial metric regular stream dyadic realSeal transport replay
        provenance localCert : BHist) :
      CauchyCompletionComparisonUp
  deriving DecidableEq

def cauchyCompletionComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionComparisonEncodeBHist h

def cauchyCompletionComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionComparisonDecodeBHist tail)

private theorem CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionComparisonDecodeBHist (cauchyCompletionComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionComparisonFields : CauchyCompletionComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionComparisonUp.mk unit universal functorial metric regular stream dyadic
      realSeal transport replay provenance localCert =>
      [unit, universal, functorial, metric, regular, stream, dyadic, realSeal, transport,
        replay, provenance, localCert]

def cauchyCompletionComparisonToEventFlow : CauchyCompletionComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCompletionComparisonFields x).map cauchyCompletionComparisonEncodeBHist

def cauchyCompletionComparisonFromEventFlow : EventFlow → Option CauchyCompletionComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | unit :: rest0 =>
      match rest0 with
      | [] => none
      | universal :: rest1 =>
          match rest1 with
          | [] => none
          | functorial :: rest2 =>
              match rest2 with
              | [] => none
              | metric :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | stream :: rest5 =>
                          match rest5 with
                          | [] => none
                          | dyadic :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localCert :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (CauchyCompletionComparisonUp.mk
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            unit)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            universal)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            functorial)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            metric)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            regular)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            stream)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            dyadic)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            realSeal)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            transport)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            replay)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            provenance)
                                                          (cauchyCompletionComparisonDecodeBHist
                                                            localCert))
                                                  | _ :: _ => none

theorem CauchyCompletionComparisonTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionComparisonUp) :
    cauchyCompletionComparisonFromEventFlow (cauchyCompletionComparisonToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk unit universal functorial metric regular stream dyadic realSeal transport replay
      provenance localCert =>
      change
        some
          (CauchyCompletionComparisonUp.mk
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist unit))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist universal))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist functorial))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist metric))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist regular))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist stream))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist dyadic))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist realSeal))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist transport))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist replay))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist provenance))
            (cauchyCompletionComparisonDecodeBHist
              (cauchyCompletionComparisonEncodeBHist localCert))) =
          some
            (CauchyCompletionComparisonUp.mk unit universal functorial metric regular stream
              dyadic realSeal transport replay provenance localCert)
      rw [CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode unit,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode universal,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode functorial,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode metric,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode regular,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode stream,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode dyadic,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode localCert]

theorem CauchyCompletionComparisonTasteGate_single_carrier_alignment_injective
    {x y : CauchyCompletionComparisonUp} :
    cauchyCompletionComparisonToEventFlow x = cauchyCompletionComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionComparisonFromEventFlow (cauchyCompletionComparisonToEventFlow x) =
        cauchyCompletionComparisonFromEventFlow (cauchyCompletionComparisonToEventFlow y) :=
    congrArg cauchyCompletionComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionComparisonTasteGate_single_carrier_alignment_round_trip y)))

theorem CauchyCompletionComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionComparisonDecodeBHist (cauchyCompletionComparisonEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionComparisonUp,
        cauchyCompletionComparisonFromEventFlow (cauchyCompletionComparisonToEventFlow x) =
          some x) ∧
        cauchyCompletionComparisonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionComparisonTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionComparisonTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyCompletionComparisonUp
