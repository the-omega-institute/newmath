import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# DimLiftBoundaryUp carrier.
-/

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite dimension-lift refusal boundary packet with the nine displayed BEDC rows. -/
inductive DimLiftBoundaryUp : Type where
  | mk :
      (carry normal cannotClaim fullAxis realRefusal transport route provenance name : BHist) →
      DimLiftBoundaryUp
  deriving DecidableEq

def dimLiftBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dimLiftBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dimLiftBoundaryEncodeBHist h

def dimLiftBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dimLiftBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dimLiftBoundaryDecodeBHist tail)

private theorem DimLiftBoundaryPacket_single_carrier_alignment_decode :
    ∀ h : BHist, dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dimLiftBoundaryToEventFlow : DimLiftBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route provenance
      name =>
      [[BMark.b0],
        dimLiftBoundaryEncodeBHist carry,
        [BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist normal,
        [BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist fullAxis,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist realRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dimLiftBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist name]

def dimLiftBoundaryFromEventFlow : EventFlow → Option DimLiftBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | carry :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | normal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cannotClaim :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fullAxis :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realRefusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (DimLiftBoundaryUp.mk
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    carry)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    normal)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    cannotClaim)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    fullAxis)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    realRefusal)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    transport)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    route)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    provenance)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem DimLiftBoundaryPacket_single_carrier_alignment_round :
    ∀ x : DimLiftBoundaryUp,
      dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carry normal cannotClaim fullAxis realRefusal transport route provenance name =>
      change
        some
          (DimLiftBoundaryUp.mk
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist carry))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name))) =
          some
            (DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
              provenance name)
      have hmk :
          DimLiftBoundaryUp.mk
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist carry))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) =
            DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
              provenance name := by
        calc
          DimLiftBoundaryUp.mk
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist carry))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) =
              DimLiftBoundaryUp.mk carry
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode carry)
          _ = DimLiftBoundaryUp.mk carry normal
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode normal)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode cannotClaim)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode fullAxis)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode realRefusal)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode transport)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                transport z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode route)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
                provenance (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                transport route z (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode provenance)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
                provenance name :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                transport route provenance z)
              (DimLiftBoundaryPacket_single_carrier_alignment_decode name)
      exact congrArg Option.some hmk

private theorem DimLiftBoundaryPacket_single_carrier_alignment_injective {x y : DimLiftBoundaryUp} :
    dimLiftBoundaryToEventFlow x = dimLiftBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) =
        dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow y) :=
    congrArg dimLiftBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DimLiftBoundaryPacket_single_carrier_alignment_round x).symm
      (Eq.trans hread (DimLiftBoundaryPacket_single_carrier_alignment_round y)))

instance dimLiftBoundaryBHistCarrier : BHistCarrier DimLiftBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dimLiftBoundaryToEventFlow
  fromEventFlow := dimLiftBoundaryFromEventFlow

instance dimLiftBoundaryChapterTasteGate : ChapterTasteGate DimLiftBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) = some x
    exact DimLiftBoundaryPacket_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DimLiftBoundaryPacket_single_carrier_alignment_injective heq)

theorem DimLiftBoundaryPacket_single_carrier_alignment :
    dimLiftBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist, dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist h) = h) ∧
        (∀ x : DimLiftBoundaryUp,
          dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact DimLiftBoundaryPacket_single_carrier_alignment_decode
    · exact DimLiftBoundaryPacket_single_carrier_alignment_round

end BEDC.Derived.DimLiftBoundaryUp
