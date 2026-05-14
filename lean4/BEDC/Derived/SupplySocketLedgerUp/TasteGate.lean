import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SupplySocketLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SupplySocketLedgerUp : Type where
  | mk :
      (gapTag supplyKind socketSite auditGate consumptionRoute provenance nameCert : BHist) →
      SupplySocketLedgerUp
  deriving DecidableEq

private def supplySocketLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: supplySocketLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: supplySocketLedgerEncodeBHist h

private def supplySocketLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (supplySocketLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (supplySocketLedgerDecodeBHist tail)

private theorem supplySocketLedgerDecode_encode_bhist :
    ∀ h : BHist, supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem supplySocketLedger_mk_congr
    {gapTag gapTag' supplyKind supplyKind' socketSite socketSite' auditGate auditGate'
      consumptionRoute consumptionRoute' provenance provenance' nameCert nameCert' : BHist}
    (hGapTag : gapTag' = gapTag)
    (hSupplyKind : supplyKind' = supplyKind)
    (hSocketSite : socketSite' = socketSite)
    (hAuditGate : auditGate' = auditGate)
    (hConsumptionRoute : consumptionRoute' = consumptionRoute)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    SupplySocketLedgerUp.mk gapTag' supplyKind' socketSite' auditGate' consumptionRoute'
        provenance' nameCert' =
      SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGapTag
  cases hSupplyKind
  cases hSocketSite
  cases hAuditGate
  cases hConsumptionRoute
  cases hProvenance
  cases hNameCert
  rfl

private def supplySocketLedgerToEventFlow : SupplySocketLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
      provenance nameCert =>
      [[BMark.b0],
        supplySocketLedgerEncodeBHist gapTag,
        [BMark.b1, BMark.b0],
        supplySocketLedgerEncodeBHist supplyKind,
        [BMark.b1, BMark.b1, BMark.b0],
        supplySocketLedgerEncodeBHist socketSite,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplySocketLedgerEncodeBHist auditGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplySocketLedgerEncodeBHist consumptionRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplySocketLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        supplySocketLedgerEncodeBHist nameCert]

private def supplySocketLedgerFromEventFlow : EventFlow → Option SupplySocketLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gapTag :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | supplyKind :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | socketSite :: rest5 =>
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
                                      | consumptionRoute :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameCert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (SupplySocketLedgerUp.mk
                                                                  (supplySocketLedgerDecodeBHist
                                                                    gapTag)
                                                                  (supplySocketLedgerDecodeBHist
                                                                    supplyKind)
                                                                  (supplySocketLedgerDecodeBHist
                                                                    socketSite)
                                                                  (supplySocketLedgerDecodeBHist
                                                                    auditGate)
                                                                  (supplySocketLedgerDecodeBHist
                                                                    consumptionRoute)
                                                                  (supplySocketLedgerDecodeBHist
                                                                    provenance)
                                                                  (supplySocketLedgerDecodeBHist
                                                                    nameCert))
                                                          | _ :: _ => none

private theorem supplySocketLedger_round_trip :
    ∀ x : SupplySocketLedgerUp,
      supplySocketLedgerFromEventFlow (supplySocketLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gapTag supplyKind socketSite auditGate consumptionRoute provenance nameCert =>
      change
        some
          (SupplySocketLedgerUp.mk
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist gapTag))
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist supplyKind))
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist socketSite))
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist auditGate))
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist consumptionRoute))
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist provenance))
            (supplySocketLedgerDecodeBHist (supplySocketLedgerEncodeBHist nameCert))) =
          some
            (SupplySocketLedgerUp.mk gapTag supplyKind socketSite auditGate consumptionRoute
              provenance nameCert)
      exact
        congrArg some
          (supplySocketLedger_mk_congr
            (supplySocketLedgerDecode_encode_bhist gapTag)
            (supplySocketLedgerDecode_encode_bhist supplyKind)
            (supplySocketLedgerDecode_encode_bhist socketSite)
            (supplySocketLedgerDecode_encode_bhist auditGate)
            (supplySocketLedgerDecode_encode_bhist consumptionRoute)
            (supplySocketLedgerDecode_encode_bhist provenance)
            (supplySocketLedgerDecode_encode_bhist nameCert))

private theorem supplySocketLedgerToEventFlow_injective {x y : SupplySocketLedgerUp} :
    supplySocketLedgerToEventFlow x = supplySocketLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      supplySocketLedgerFromEventFlow (supplySocketLedgerToEventFlow x) =
        supplySocketLedgerFromEventFlow (supplySocketLedgerToEventFlow y) :=
    congrArg supplySocketLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (supplySocketLedger_round_trip x).symm
      (Eq.trans hread (supplySocketLedger_round_trip y)))

instance supplySocketLedgerBHistCarrier : BHistCarrier SupplySocketLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := supplySocketLedgerToEventFlow
  fromEventFlow := supplySocketLedgerFromEventFlow

instance supplySocketLedgerChapterTasteGate : ChapterTasteGate SupplySocketLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change supplySocketLedgerFromEventFlow (supplySocketLedgerToEventFlow x) = some x
    exact supplySocketLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (supplySocketLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SupplySocketLedgerUp :=
  supplySocketLedgerChapterTasteGate

theorem SupplySocketLedgerTasteGate_single_carrier_alignment :
    supplySocketLedgerFromEventFlow
        (supplySocketLedgerToEventFlow
          (SupplySocketLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty)) =
      some
        (SupplySocketLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact supplySocketLedger_round_trip
    (SupplySocketLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty)

end BEDC.Derived.SupplySocketLedgerUp
