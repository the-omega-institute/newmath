import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SupplyKindRouterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SupplyKindRouterUp : Type where
  | mk :
      (site kind requestedShape auditGate transport route provenance nameCert : BHist) →
      SupplyKindRouterUp
  deriving DecidableEq

def supplyKindRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: supplyKindRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: supplyKindRouterEncodeBHist h

def supplyKindRouterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (supplyKindRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (supplyKindRouterDecodeBHist tail)

private theorem SupplyKindRouterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, supplyKindRouterDecodeBHist (supplyKindRouterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem SupplyKindRouterTasteGate_single_carrier_alignment_mk_congr
    {site site' kind kind' requestedShape requestedShape' auditGate auditGate'
      transport transport' route route' provenance provenance' nameCert nameCert' : BHist}
    (hSite : site' = site)
    (hKind : kind' = kind)
    (hRequestedShape : requestedShape' = requestedShape)
    (hAuditGate : auditGate' = auditGate)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    SupplyKindRouterUp.mk site' kind' requestedShape' auditGate' transport' route' provenance'
        nameCert' =
      SupplyKindRouterUp.mk site kind requestedShape auditGate transport route provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSite
  cases hKind
  cases hRequestedShape
  cases hAuditGate
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def supplyKindRouterToEventFlow : SupplyKindRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SupplyKindRouterUp.mk site kind requestedShape auditGate transport route provenance
      nameCert =>
      [[BMark.b0],
        supplyKindRouterEncodeBHist site,
        [BMark.b1, BMark.b0],
        supplyKindRouterEncodeBHist kind,
        [BMark.b1, BMark.b1, BMark.b0],
        supplyKindRouterEncodeBHist requestedShape,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplyKindRouterEncodeBHist auditGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplyKindRouterEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplyKindRouterEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplyKindRouterEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        supplyKindRouterEncodeBHist nameCert]

private def supplyKindRouterDecodePacket
    (site kind requestedShape auditGate transport route provenance nameCert : RawEvent) :
    SupplyKindRouterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SupplyKindRouterUp.mk
    (supplyKindRouterDecodeBHist site)
    (supplyKindRouterDecodeBHist kind)
    (supplyKindRouterDecodeBHist requestedShape)
    (supplyKindRouterDecodeBHist auditGate)
    (supplyKindRouterDecodeBHist transport)
    (supplyKindRouterDecodeBHist route)
    (supplyKindRouterDecodeBHist provenance)
    (supplyKindRouterDecodeBHist nameCert)

def supplyKindRouterFromEventFlow : EventFlow → Option SupplyKindRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | site :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | kind :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | requestedShape :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditGate :: rest7 =>
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
                                              | route :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (supplyKindRouterDecodePacket
                                                                          site kind
                                                                          requestedShape
                                                                          auditGate
                                                                          transport route
                                                                          provenance nameCert)
                                                                  | _ :: _ => none

private theorem SupplyKindRouterTasteGate_single_carrier_alignment_round :
    ∀ x : SupplyKindRouterUp,
      supplyKindRouterFromEventFlow (supplyKindRouterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk site kind requestedShape auditGate transport route provenance nameCert =>
      change
        some
          (supplyKindRouterDecodePacket
            (supplyKindRouterEncodeBHist site)
            (supplyKindRouterEncodeBHist kind)
            (supplyKindRouterEncodeBHist requestedShape)
            (supplyKindRouterEncodeBHist auditGate)
            (supplyKindRouterEncodeBHist transport)
            (supplyKindRouterEncodeBHist route)
            (supplyKindRouterEncodeBHist provenance)
            (supplyKindRouterEncodeBHist nameCert)) =
          some
            (SupplyKindRouterUp.mk site kind requestedShape auditGate transport route provenance
              nameCert)
      unfold supplyKindRouterDecodePacket
      exact
        congrArg some
          (SupplyKindRouterTasteGate_single_carrier_alignment_mk_congr
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode site)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode kind)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode requestedShape)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode auditGate)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode transport)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode route)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode provenance)
            (SupplyKindRouterTasteGate_single_carrier_alignment_decode nameCert))

private theorem SupplyKindRouterTasteGate_single_carrier_alignment_injective
    {x y : SupplyKindRouterUp} :
    supplyKindRouterToEventFlow x = supplyKindRouterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      supplyKindRouterFromEventFlow (supplyKindRouterToEventFlow x) =
        supplyKindRouterFromEventFlow (supplyKindRouterToEventFlow y) :=
    congrArg supplyKindRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SupplyKindRouterTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread (SupplyKindRouterTasteGate_single_carrier_alignment_round y)))

instance supplyKindRouterBHistCarrier : BHistCarrier SupplyKindRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := supplyKindRouterToEventFlow
  fromEventFlow := supplyKindRouterFromEventFlow

instance supplyKindRouterChapterTasteGate : ChapterTasteGate SupplyKindRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change supplyKindRouterFromEventFlow (supplyKindRouterToEventFlow x) = some x
    exact SupplyKindRouterTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SupplyKindRouterTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SupplyKindRouterUp :=
  supplyKindRouterChapterTasteGate

theorem SupplyKindRouterTasteGate_single_carrier_alignment :
    (forall h : BHist, supplyKindRouterDecodeBHist (supplyKindRouterEncodeBHist h) = h) /\
      (forall x : SupplyKindRouterUp,
        supplyKindRouterFromEventFlow (supplyKindRouterToEventFlow x) = some x) /\
        (forall x y : SupplyKindRouterUp,
          supplyKindRouterToEventFlow x = supplyKindRouterToEventFlow y -> x = y) /\
          supplyKindRouterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact And.intro SupplyKindRouterTasteGate_single_carrier_alignment_decode
    (And.intro SupplyKindRouterTasteGate_single_carrier_alignment_round
      (And.intro
        (by
          intro x y heq
          exact SupplyKindRouterTasteGate_single_carrier_alignment_injective heq)
        rfl))

end BEDC.Derived.SupplyKindRouterUp
