import BEDC.Derived.HyperbolicBoundaryTransportUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicBoundaryTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def hyperbolicBoundaryTransportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicBoundaryTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicBoundaryTransportEncodeBHist h

def hyperbolicBoundaryTransportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicBoundaryTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicBoundaryTransportDecodeBHist tail)

private theorem hyperbolicBoundaryTransport_decode_encode_bhist :
    ∀ h : BHist,
      hyperbolicBoundaryTransportDecodeBHist
        (hyperbolicBoundaryTransportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicBoundaryTransportFields :
    BEDC.Derived.HyperbolicBoundaryTransportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.HyperbolicBoundaryTransportUp.mk diskMap boundaryFarEnd
      reversibleTransport provenance transport replay metricNoncollapse localCert =>
      [diskMap, boundaryFarEnd, reversibleTransport, provenance, transport, replay,
        metricNoncollapse, localCert]

def hyperbolicBoundaryTransportToEventFlow :
    BEDC.Derived.HyperbolicBoundaryTransportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map hyperbolicBoundaryTransportEncodeBHist
      (hyperbolicBoundaryTransportFields x)

def hyperbolicBoundaryTransportFromEventFlow :
    EventFlow → Option BEDC.Derived.HyperbolicBoundaryTransportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | diskMap :: rest0 =>
      match rest0 with
      | [] => none
      | boundaryFarEnd :: rest1 =>
          match rest1 with
          | [] => none
          | reversibleTransport :: rest2 =>
              match rest2 with
              | [] => none
              | provenance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | replay :: rest5 =>
                          match rest5 with
                          | [] => none
                          | metricNoncollapse :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localCert :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (BEDC.Derived.HyperbolicBoundaryTransportUp.mk
                                          (hyperbolicBoundaryTransportDecodeBHist diskMap)
                                          (hyperbolicBoundaryTransportDecodeBHist boundaryFarEnd)
                                          (hyperbolicBoundaryTransportDecodeBHist
                                            reversibleTransport)
                                          (hyperbolicBoundaryTransportDecodeBHist provenance)
                                          (hyperbolicBoundaryTransportDecodeBHist transport)
                                          (hyperbolicBoundaryTransportDecodeBHist replay)
                                          (hyperbolicBoundaryTransportDecodeBHist
                                            metricNoncollapse)
                                          (hyperbolicBoundaryTransportDecodeBHist localCert))
                                  | _ :: _ => none

private theorem HyperbolicBoundaryTransportTasteGate_single_carrier_alignment_mk_congr
    {D1 D2 F1 F2 R1 R2 P1 P2 H1 H2 T1 T2 M1 M2 N1 N2 : BHist}
    (hD : D1 = D2) (hF : F1 = F2) (hR : R1 = R2) (hP : P1 = P2)
    (hH : H1 = H2) (hT : T1 = T2) (hM : M1 = M2) (hN : N1 = N2) :
    BEDC.Derived.HyperbolicBoundaryTransportUp.mk D1 F1 R1 P1 H1 T1 M1 N1 =
      BEDC.Derived.HyperbolicBoundaryTransportUp.mk D2 F2 R2 P2 H2 T2 M2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hF
  cases hR
  cases hP
  cases hH
  cases hT
  cases hM
  cases hN
  rfl

private theorem hyperbolicBoundaryTransport_round_trip :
    ∀ x : BEDC.Derived.HyperbolicBoundaryTransportUp,
      hyperbolicBoundaryTransportFromEventFlow
        (hyperbolicBoundaryTransportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk diskMap boundaryFarEnd reversibleTransport provenance transport replay
      metricNoncollapse localCert =>
      change
        some
          (BEDC.Derived.HyperbolicBoundaryTransportUp.mk
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist diskMap))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist boundaryFarEnd))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist reversibleTransport))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist provenance))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist transport))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist replay))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist metricNoncollapse))
            (hyperbolicBoundaryTransportDecodeBHist
              (hyperbolicBoundaryTransportEncodeBHist localCert))) =
          some
            (BEDC.Derived.HyperbolicBoundaryTransportUp.mk diskMap boundaryFarEnd
              reversibleTransport provenance transport replay metricNoncollapse localCert)
      exact
        congrArg some
          (HyperbolicBoundaryTransportTasteGate_single_carrier_alignment_mk_congr
            (hyperbolicBoundaryTransport_decode_encode_bhist diskMap)
            (hyperbolicBoundaryTransport_decode_encode_bhist boundaryFarEnd)
            (hyperbolicBoundaryTransport_decode_encode_bhist reversibleTransport)
            (hyperbolicBoundaryTransport_decode_encode_bhist provenance)
            (hyperbolicBoundaryTransport_decode_encode_bhist transport)
            (hyperbolicBoundaryTransport_decode_encode_bhist replay)
            (hyperbolicBoundaryTransport_decode_encode_bhist metricNoncollapse)
            (hyperbolicBoundaryTransport_decode_encode_bhist localCert))

private theorem hyperbolicBoundaryTransportToEventFlow_injective
    {x y : BEDC.Derived.HyperbolicBoundaryTransportUp} :
    hyperbolicBoundaryTransportToEventFlow x = hyperbolicBoundaryTransportToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicBoundaryTransportFromEventFlow (hyperbolicBoundaryTransportToEventFlow x) =
        hyperbolicBoundaryTransportFromEventFlow (hyperbolicBoundaryTransportToEventFlow y) :=
    congrArg hyperbolicBoundaryTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicBoundaryTransport_round_trip x).symm
      (Eq.trans hread (hyperbolicBoundaryTransport_round_trip y)))

instance hyperbolicBoundaryTransportBHistCarrier :
    BHistCarrier BEDC.Derived.HyperbolicBoundaryTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicBoundaryTransportToEventFlow
  fromEventFlow := hyperbolicBoundaryTransportFromEventFlow

instance hyperbolicBoundaryTransportChapterTasteGate :
    ChapterTasteGate BEDC.Derived.HyperbolicBoundaryTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicBoundaryTransportFromEventFlow
        (hyperbolicBoundaryTransportToEventFlow x) = some x
    exact hyperbolicBoundaryTransport_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicBoundaryTransportToEventFlow_injective heq)

theorem HyperbolicBoundaryTransportTasteGate_single_carrier_alignment :
    (hyperbolicBoundaryTransportEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist,
        hyperbolicBoundaryTransportDecodeBHist
          (hyperbolicBoundaryTransportEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.HyperbolicBoundaryTransportUp,
        hyperbolicBoundaryTransportFromEventFlow
          (hyperbolicBoundaryTransportToEventFlow x) = some x) ∧
      (∀ x y : BEDC.Derived.HyperbolicBoundaryTransportUp,
        hyperbolicBoundaryTransportToEventFlow x =
          hyperbolicBoundaryTransportToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl,
      hyperbolicBoundaryTransport_decode_encode_bhist,
      hyperbolicBoundaryTransport_round_trip,
      fun _ _ heq => hyperbolicBoundaryTransportToEventFlow_injective heq⟩

end BEDC.Derived.HyperbolicBoundaryTransportUp
