import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCofinalTailSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCofinalTailSelectorUp : Type where
  | mk :
      (request dyadicFamily selectedTail windowReadback regseqReadback realSeal transport routes
        provenance nameCert : BHist) →
      DyadicCofinalTailSelectorUp
  deriving DecidableEq

private def dyadicCofinalTailSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCofinalTailSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCofinalTailSelectorEncodeBHist h

private def dyadicCofinalTailSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCofinalTailSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCofinalTailSelectorDecodeBHist tail)

private theorem dyadicCofinalTailSelectorDecode_encode_bhist :
    ∀ h : BHist,
      dyadicCofinalTailSelectorDecodeBHist (dyadicCofinalTailSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem dyadicCofinalTailSelector_mk_congr
    {request request' dyadicFamily dyadicFamily' selectedTail selectedTail'
      windowReadback windowReadback' regseqReadback regseqReadback' realSeal realSeal'
      transport transport' routes routes' provenance provenance' nameCert nameCert' : BHist}
    (hRequest : request' = request)
    (hDyadicFamily : dyadicFamily' = dyadicFamily)
    (hSelectedTail : selectedTail' = selectedTail)
    (hWindowReadback : windowReadback' = windowReadback)
    (hRegseqReadback : regseqReadback' = regseqReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    DyadicCofinalTailSelectorUp.mk request' dyadicFamily' selectedTail' windowReadback'
        regseqReadback' realSeal' transport' routes' provenance' nameCert' =
      DyadicCofinalTailSelectorUp.mk request dyadicFamily selectedTail windowReadback
        regseqReadback realSeal transport routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRequest
  cases hDyadicFamily
  cases hSelectedTail
  cases hWindowReadback
  cases hRegseqReadback
  cases hRealSeal
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private def dyadicCofinalTailSelectorToEventFlow : DyadicCofinalTailSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCofinalTailSelectorUp.mk request dyadicFamily selectedTail windowReadback
      regseqReadback realSeal transport routes provenance nameCert =>
      [[BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist request,
        [BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist dyadicFamily,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist selectedTail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist windowReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist regseqReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dyadicCofinalTailSelectorEncodeBHist nameCert]

private def dyadicCofinalTailSelectorFromEventFlow : EventFlow → Option DyadicCofinalTailSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | dyadicFamily :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selectedTail :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | windowReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | regseqReadback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realSeal :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (DyadicCofinalTailSelectorUp.mk
                                                                                          (dyadicCofinalTailSelectorDecodeBHist request)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist dyadicFamily)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist selectedTail)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist windowReadback)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist regseqReadback)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist realSeal)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist transport)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist routes)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist provenance)
                                                                                          (dyadicCofinalTailSelectorDecodeBHist nameCert))
                                                                                  | _ :: _ => none

private theorem dyadicCofinalTailSelector_round_trip :
    ∀ x : DyadicCofinalTailSelectorUp,
      dyadicCofinalTailSelectorFromEventFlow
        (dyadicCofinalTailSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request dyadicFamily selectedTail windowReadback regseqReadback realSeal transport
      routes provenance nameCert =>
      change
        some
          (DyadicCofinalTailSelectorUp.mk
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist request))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist dyadicFamily))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist selectedTail))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist windowReadback))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist regseqReadback))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist realSeal))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist transport))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist routes))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist provenance))
            (dyadicCofinalTailSelectorDecodeBHist
              (dyadicCofinalTailSelectorEncodeBHist nameCert))) =
          some
            (DyadicCofinalTailSelectorUp.mk request dyadicFamily selectedTail
              windowReadback regseqReadback realSeal transport routes provenance nameCert)
      exact
        congrArg some
          (dyadicCofinalTailSelector_mk_congr
            (dyadicCofinalTailSelectorDecode_encode_bhist request)
            (dyadicCofinalTailSelectorDecode_encode_bhist dyadicFamily)
            (dyadicCofinalTailSelectorDecode_encode_bhist selectedTail)
            (dyadicCofinalTailSelectorDecode_encode_bhist windowReadback)
            (dyadicCofinalTailSelectorDecode_encode_bhist regseqReadback)
            (dyadicCofinalTailSelectorDecode_encode_bhist realSeal)
            (dyadicCofinalTailSelectorDecode_encode_bhist transport)
            (dyadicCofinalTailSelectorDecode_encode_bhist routes)
            (dyadicCofinalTailSelectorDecode_encode_bhist provenance)
            (dyadicCofinalTailSelectorDecode_encode_bhist nameCert))

private theorem dyadicCofinalTailSelectorToEventFlow_injective
    {x y : DyadicCofinalTailSelectorUp} :
    dyadicCofinalTailSelectorToEventFlow x = dyadicCofinalTailSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCofinalTailSelectorFromEventFlow (dyadicCofinalTailSelectorToEventFlow x) =
        dyadicCofinalTailSelectorFromEventFlow (dyadicCofinalTailSelectorToEventFlow y) :=
    congrArg dyadicCofinalTailSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicCofinalTailSelector_round_trip x).symm
      (Eq.trans hread (dyadicCofinalTailSelector_round_trip y)))

instance dyadicCofinalTailSelectorBHistCarrier :
    BHistCarrier DyadicCofinalTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCofinalTailSelectorToEventFlow
  fromEventFlow := dyadicCofinalTailSelectorFromEventFlow

instance dyadicCofinalTailSelectorChapterTasteGate :
    ChapterTasteGate DyadicCofinalTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCofinalTailSelectorFromEventFlow
      (dyadicCofinalTailSelectorToEventFlow x) = some x
    exact dyadicCofinalTailSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicCofinalTailSelectorToEventFlow_injective heq)

instance dyadicCofinalTailSelectorFieldFaithful :
    FieldFaithful DyadicCofinalTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | DyadicCofinalTailSelectorUp.mk request dyadicFamily selectedTail windowReadback
        regseqReadback realSeal transport routes provenance nameCert =>
        [request, dyadicFamily, selectedTail, windowReadback, regseqReadback, realSeal,
          transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk request₁ dyadicFamily₁ selectedTail₁ windowReadback₁ regseqReadback₁ realSeal₁
        transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk request₂ dyadicFamily₂ selectedTail₂ windowReadback₂ regseqReadback₂ realSeal₂
            transport₂ routes₂ provenance₂ nameCert₂ =>
            cases h
            rfl

theorem DyadicCofinalTailSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicCofinalTailSelectorDecodeBHist
        (dyadicCofinalTailSelectorEncodeBHist h) = h) ∧
      (∀ x : DyadicCofinalTailSelectorUp,
        dyadicCofinalTailSelectorFromEventFlow
          (dyadicCofinalTailSelectorToEventFlow x) = some x) ∧
        (∀ x y : DyadicCofinalTailSelectorUp,
          dyadicCofinalTailSelectorToEventFlow x =
            dyadicCofinalTailSelectorToEventFlow y → x = y) ∧
          dyadicCofinalTailSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicCofinalTailSelectorDecode_encode_bhist
  · constructor
    · exact dyadicCofinalTailSelector_round_trip
    · constructor
      · intro x y heq
        exact dyadicCofinalTailSelectorToEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicCofinalTailSelectorUp
