import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscribedRouteSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscribedRouteSelectorUp : Type where
  | mk : (gap mark route check use ledger hsameRow contRow provenance name : BHist) →
      InscribedRouteSelectorUp
  deriving DecidableEq

def inscribedRouteSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscribedRouteSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscribedRouteSelectorEncodeBHist h

def inscribedRouteSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscribedRouteSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscribedRouteSelectorDecodeBHist tail)

private theorem inscribedRouteSelectorDecode_encode_bhist :
    ∀ h : BHist,
      inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inscribedRouteSelector_mk_congr
    {gap gap' mark mark' route route' check check' use use' ledger ledger' hsameRow
      hsameRow' contRow contRow' provenance provenance' name name' : BHist}
    (hGap : gap' = gap)
    (hMark : mark' = mark)
    (hRoute : route' = route)
    (hCheck : check' = check)
    (hUse : use' = use)
    (hLedger : ledger' = ledger)
    (hHsame : hsameRow' = hsameRow)
    (hCont : contRow' = contRow)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    InscribedRouteSelectorUp.mk gap' mark' route' check' use' ledger' hsameRow' contRow'
        provenance' name' =
      InscribedRouteSelectorUp.mk gap mark route check use ledger hsameRow contRow provenance
        name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGap
  cases hMark
  cases hRoute
  cases hCheck
  cases hUse
  cases hLedger
  cases hHsame
  cases hCont
  cases hProvenance
  cases hName
  rfl

def inscribedRouteSelectorToEventFlow : InscribedRouteSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscribedRouteSelectorUp.mk gap mark route check use ledger hsameRow contRow provenance
      name =>
      [[BMark.b0],
        inscribedRouteSelectorEncodeBHist gap,
        [BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist mark,
        [BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist check,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist use,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist hsameRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscribedRouteSelectorEncodeBHist contRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteSelectorEncodeBHist name]

def inscribedRouteSelectorFromEventFlow : EventFlow → Option InscribedRouteSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gap :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | mark :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | check :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | use :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | hsameRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | contRow :: rest15 =>
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
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (InscribedRouteSelectorUp.mk
                                                                                          (inscribedRouteSelectorDecodeBHist gap)
                                                                                          (inscribedRouteSelectorDecodeBHist mark)
                                                                                          (inscribedRouteSelectorDecodeBHist route)
                                                                                          (inscribedRouteSelectorDecodeBHist check)
                                                                                          (inscribedRouteSelectorDecodeBHist use)
                                                                                          (inscribedRouteSelectorDecodeBHist ledger)
                                                                                          (inscribedRouteSelectorDecodeBHist hsameRow)
                                                                                          (inscribedRouteSelectorDecodeBHist contRow)
                                                                                          (inscribedRouteSelectorDecodeBHist provenance)
                                                                                          (inscribedRouteSelectorDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem inscribedRouteSelector_round_trip :
    ∀ x : InscribedRouteSelectorUp,
      inscribedRouteSelectorFromEventFlow (inscribedRouteSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gap mark route check use ledger hsameRow contRow provenance name =>
      change
        some
          (InscribedRouteSelectorUp.mk
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist gap))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist mark))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist route))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist check))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist use))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist ledger))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist hsameRow))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist contRow))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist provenance))
            (inscribedRouteSelectorDecodeBHist (inscribedRouteSelectorEncodeBHist name))) =
          some
            (InscribedRouteSelectorUp.mk gap mark route check use ledger hsameRow contRow
              provenance name)
      exact
        congrArg some
          (inscribedRouteSelector_mk_congr
            (inscribedRouteSelectorDecode_encode_bhist gap)
            (inscribedRouteSelectorDecode_encode_bhist mark)
            (inscribedRouteSelectorDecode_encode_bhist route)
            (inscribedRouteSelectorDecode_encode_bhist check)
            (inscribedRouteSelectorDecode_encode_bhist use)
            (inscribedRouteSelectorDecode_encode_bhist ledger)
            (inscribedRouteSelectorDecode_encode_bhist hsameRow)
            (inscribedRouteSelectorDecode_encode_bhist contRow)
            (inscribedRouteSelectorDecode_encode_bhist provenance)
            (inscribedRouteSelectorDecode_encode_bhist name))

private theorem inscribedRouteSelectorToEventFlow_injective
    {x y : InscribedRouteSelectorUp} :
    inscribedRouteSelectorToEventFlow x = inscribedRouteSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscribedRouteSelectorFromEventFlow (inscribedRouteSelectorToEventFlow x) =
        inscribedRouteSelectorFromEventFlow (inscribedRouteSelectorToEventFlow y) :=
    congrArg inscribedRouteSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscribedRouteSelector_round_trip x).symm
      (Eq.trans hread (inscribedRouteSelector_round_trip y)))

instance inscribedRouteSelectorBHistCarrier :
    BHistCarrier InscribedRouteSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscribedRouteSelectorToEventFlow
  fromEventFlow := inscribedRouteSelectorFromEventFlow

instance inscribedRouteSelectorChapterTasteGate :
    ChapterTasteGate InscribedRouteSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscribedRouteSelectorFromEventFlow (inscribedRouteSelectorToEventFlow x) =
      some x
    exact inscribedRouteSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscribedRouteSelectorToEventFlow_injective heq)

instance inscribedRouteSelectorFieldFaithful :
    FieldFaithful InscribedRouteSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | InscribedRouteSelectorUp.mk gap mark route check use ledger hsameRow contRow provenance
        name =>
        [gap, mark, route, check, use, ledger, hsameRow, contRow, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk gap₁ mark₁ route₁ check₁ use₁ ledger₁ hsame₁ cont₁ provenance₁ name₁ =>
        cases y with
        | mk gap₂ mark₂ route₂ check₂ use₂ ledger₂ hsame₂ cont₂ provenance₂ name₂ =>
            injection h with hGap t1
            injection t1 with hMark t2
            injection t2 with hRoute t3
            injection t3 with hCheck t4
            injection t4 with hUse t5
            injection t5 with hLedger t6
            injection t6 with hHsame t7
            injection t7 with hCont t8
            injection t8 with hProvenance t9
            injection t9 with hName _
            cases hGap
            cases hMark
            cases hRoute
            cases hCheck
            cases hUse
            cases hLedger
            cases hHsame
            cases hCont
            cases hProvenance
            cases hName
            rfl

instance inscribedRouteSelectorNontrivial :
    Nontrivial InscribedRouteSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InscribedRouteSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscribedRouteSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscribedRouteSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem InscribedRouteSelectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate InscribedRouteSelectorUp) ∧
      Nonempty (FieldFaithful InscribedRouteSelectorUp) ∧
      Nonempty (Nontrivial InscribedRouteSelectorUp) ∧
        inscribedRouteSelectorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, rfl⟩

end BEDC.Derived.InscribedRouteSelectorUp
