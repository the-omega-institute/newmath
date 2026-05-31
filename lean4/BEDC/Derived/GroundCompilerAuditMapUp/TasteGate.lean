import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerAuditMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerAuditMapUp : Type where
  | mk :
      (inventory theoremCells eventFlow compilerLayer recognizers reports frontier handoff
        transport routes provenance nameCert : BHist) →
        GroundCompilerAuditMapUp
  deriving DecidableEq

def groundCompilerAuditMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerAuditMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerAuditMapEncodeBHist h

def groundCompilerAuditMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerAuditMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerAuditMapDecodeBHist tail)

private theorem groundCompilerAuditMap_decode_encode_bhist :
    ∀ h : BHist,
      groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem groundCompilerAuditMap_mk_congr
    {inventory inventory' theoremCells theoremCells' eventFlow eventFlow'
      compilerLayer compilerLayer' recognizers recognizers' reports reports' frontier frontier'
      handoff handoff' transport transport' routes routes' provenance provenance'
      nameCert nameCert' : BHist}
    (hInventory : inventory' = inventory)
    (hTheoremCells : theoremCells' = theoremCells)
    (hEventFlow : eventFlow' = eventFlow)
    (hCompilerLayer : compilerLayer' = compilerLayer)
    (hRecognizers : recognizers' = recognizers)
    (hReports : reports' = reports)
    (hFrontier : frontier' = frontier)
    (hHandoff : handoff' = handoff)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    GroundCompilerAuditMapUp.mk inventory' theoremCells' eventFlow' compilerLayer'
        recognizers' reports' frontier' handoff' transport' routes' provenance' nameCert' =
      GroundCompilerAuditMapUp.mk inventory theoremCells eventFlow compilerLayer recognizers
        reports frontier handoff transport routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hInventory
  cases hTheoremCells
  cases hEventFlow
  cases hCompilerLayer
  cases hRecognizers
  cases hReports
  cases hFrontier
  cases hHandoff
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

def groundCompilerAuditMapToEventFlow : GroundCompilerAuditMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerAuditMapUp.mk inventory theoremCells eventFlow compilerLayer recognizers
      reports frontier handoff transport routes provenance nameCert =>
      [[BMark.b0],
        groundCompilerAuditMapEncodeBHist inventory,
        [BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist theoremCells,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist eventFlow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist compilerLayer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist recognizers,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist reports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundCompilerAuditMapEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditMapEncodeBHist nameCert]

def groundCompilerAuditMapFromEventFlow : EventFlow -> Option GroundCompilerAuditMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | inventory :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | theoremCells :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | eventFlow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | compilerLayer :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | recognizers :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | reports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | frontier :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | handoff :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | routes :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | nameCert :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (GroundCompilerAuditMapUp.mk
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            inventory)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            theoremCells)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            eventFlow)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            compilerLayer)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            recognizers)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            reports)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            frontier)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            handoff)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            transport)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            routes)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            provenance)
                                                                                                          (groundCompilerAuditMapDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ :: _ => none

private theorem groundCompilerAuditMap_round_trip :
    ∀ x : GroundCompilerAuditMapUp,
      groundCompilerAuditMapFromEventFlow (groundCompilerAuditMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inventory theoremCells eventFlow compilerLayer recognizers reports frontier handoff
      transport routes provenance nameCert =>
      change
        some
          (GroundCompilerAuditMapUp.mk
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist inventory))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist theoremCells))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist eventFlow))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist compilerLayer))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist recognizers))
            (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist reports))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist frontier))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist handoff))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist transport))
            (groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist routes))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist provenance))
            (groundCompilerAuditMapDecodeBHist
              (groundCompilerAuditMapEncodeBHist nameCert))) =
          some
            (GroundCompilerAuditMapUp.mk inventory theoremCells eventFlow compilerLayer
              recognizers reports frontier handoff transport routes provenance nameCert)
      exact
        congrArg some
          (groundCompilerAuditMap_mk_congr
            (groundCompilerAuditMap_decode_encode_bhist inventory)
            (groundCompilerAuditMap_decode_encode_bhist theoremCells)
            (groundCompilerAuditMap_decode_encode_bhist eventFlow)
            (groundCompilerAuditMap_decode_encode_bhist compilerLayer)
            (groundCompilerAuditMap_decode_encode_bhist recognizers)
            (groundCompilerAuditMap_decode_encode_bhist reports)
            (groundCompilerAuditMap_decode_encode_bhist frontier)
            (groundCompilerAuditMap_decode_encode_bhist handoff)
            (groundCompilerAuditMap_decode_encode_bhist transport)
            (groundCompilerAuditMap_decode_encode_bhist routes)
            (groundCompilerAuditMap_decode_encode_bhist provenance)
            (groundCompilerAuditMap_decode_encode_bhist nameCert))

private theorem groundCompilerAuditMapToEventFlow_injective
    {x y : GroundCompilerAuditMapUp} :
    groundCompilerAuditMapToEventFlow x = groundCompilerAuditMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerAuditMapFromEventFlow (groundCompilerAuditMapToEventFlow x) =
        groundCompilerAuditMapFromEventFlow (groundCompilerAuditMapToEventFlow y) :=
    congrArg groundCompilerAuditMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerAuditMap_round_trip x).symm
      (Eq.trans hread (groundCompilerAuditMap_round_trip y)))

instance groundCompilerAuditMapBHistCarrier : BHistCarrier GroundCompilerAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerAuditMapToEventFlow
  fromEventFlow := groundCompilerAuditMapFromEventFlow

instance groundCompilerAuditMapChapterTasteGate : ChapterTasteGate GroundCompilerAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change groundCompilerAuditMapFromEventFlow (groundCompilerAuditMapToEventFlow x) = some x
    exact groundCompilerAuditMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerAuditMapToEventFlow_injective heq)

def taste_gate : ChapterTasteGate GroundCompilerAuditMapUp :=
  groundCompilerAuditMapChapterTasteGate

instance groundCompilerAuditMapFieldFaithful : FieldFaithful GroundCompilerAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | GroundCompilerAuditMapUp.mk inventory theoremCells eventFlow compilerLayer recognizers
        reports frontier handoff transport routes provenance nameCert =>
        [inventory, theoremCells, eventFlow, compilerLayer, recognizers, reports, frontier,
          handoff, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk inventory₁ theoremCells₁ eventFlow₁ compilerLayer₁ recognizers₁ reports₁ frontier₁
        handoff₁ transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk inventory₂ theoremCells₂ eventFlow₂ compilerLayer₂ recognizers₂ reports₂
            frontier₂ handoff₂ transport₂ routes₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

theorem GroundCompilerAuditMapTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      groundCompilerAuditMapDecodeBHist (groundCompilerAuditMapEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerAuditMapUp,
        groundCompilerAuditMapFromEventFlow (groundCompilerAuditMapToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerAuditMapUp,
          groundCompilerAuditMapToEventFlow x = groundCompilerAuditMapToEventFlow y → x = y) ∧
          (∀ (x : GroundCompilerAuditMapUp) w m,
            List.Mem w (groundCompilerAuditMapToEventFlow x) →
              List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) ∧
            groundCompilerAuditMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact groundCompilerAuditMap_decode_encode_bhist
  · constructor
    · exact groundCompilerAuditMap_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerAuditMapToEventFlow_injective heq
      · constructor
        · intro x w m hw hm
          exact BMark_generated_cases m
        · rfl

end BEDC.Derived.GroundCompilerAuditMapUp
