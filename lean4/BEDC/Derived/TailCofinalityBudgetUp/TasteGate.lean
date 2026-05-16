import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailCofinalityBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailCofinalityBudgetUp : Type where
  | mk :
      (threshold window dyadic readback sealRow transport route provenance name : BHist) →
      TailCofinalityBudgetUp
  deriving DecidableEq

def tailCofinalityBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailCofinalityBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailCofinalityBudgetEncodeBHist h

def tailCofinalityBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailCofinalityBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailCofinalityBudgetDecodeBHist tail)

theorem TailCofinalityBudgetTasteGate_obligation_surface_decode :
    ∀ h : BHist,
      tailCofinalityBudgetDecodeBHist (tailCofinalityBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tailCofinalityBudgetFields : TailCofinalityBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TailCofinalityBudgetUp.mk threshold window dyadic readback sealRow transport route
      provenance name =>
      [threshold, window, dyadic, readback, sealRow, transport, route, provenance, name]

theorem TailCofinalityBudgetTasteGate_obligation_surface_mk_congr
    {threshold threshold' window window' dyadic dyadic' readback readback'
      sealRow sealRow' transport transport' route route' provenance provenance' name name' :
        BHist}
    (hThreshold : threshold' = threshold)
    (hWindow : window' = window)
    (hDyadic : dyadic' = dyadic)
    (hReadback : readback' = readback)
    (hSeal : sealRow' = sealRow)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    TailCofinalityBudgetUp.mk threshold' window' dyadic' readback' sealRow' transport'
        route' provenance' name' =
      TailCofinalityBudgetUp.mk threshold window dyadic readback sealRow transport route
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hThreshold
  cases hWindow
  cases hDyadic
  cases hReadback
  cases hSeal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def tailCofinalityBudgetToEventFlow :
    TailCofinalityBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TailCofinalityBudgetUp.mk threshold window dyadic readback sealRow transport route
      provenance name =>
      [[BMark.b0],
        tailCofinalityBudgetEncodeBHist threshold,
        [BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tailCofinalityBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tailCofinalityBudgetEncodeBHist name]

def tailCofinalityBudgetFromEventFlow :
    EventFlow → Option TailCofinalityBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | threshold :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealRow :: rest9 =>
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
                                                                                (TailCofinalityBudgetUp.mk
                                                                                  (tailCofinalityBudgetDecodeBHist threshold)
                                                                                  (tailCofinalityBudgetDecodeBHist window)
                                                                                  (tailCofinalityBudgetDecodeBHist dyadic)
                                                                                  (tailCofinalityBudgetDecodeBHist readback)
                                                                                  (tailCofinalityBudgetDecodeBHist sealRow)
                                                                                  (tailCofinalityBudgetDecodeBHist transport)
                                                                                  (tailCofinalityBudgetDecodeBHist route)
                                                                                  (tailCofinalityBudgetDecodeBHist provenance)
                                                                                  (tailCofinalityBudgetDecodeBHist name))
                                                                          | _ :: _ => none

theorem TailCofinalityBudgetTasteGate_obligation_surface_round_trip :
    ∀ x : TailCofinalityBudgetUp,
      tailCofinalityBudgetFromEventFlow
        (tailCofinalityBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk threshold window dyadic readback sealRow transport route provenance name =>
      exact
        congrArg some
          (TailCofinalityBudgetTasteGate_obligation_surface_mk_congr
            (TailCofinalityBudgetTasteGate_obligation_surface_decode threshold)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode window)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode dyadic)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode readback)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode sealRow)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode transport)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode route)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode provenance)
            (TailCofinalityBudgetTasteGate_obligation_surface_decode name))

theorem TailCofinalityBudgetTasteGate_obligation_surface_injective
    {x y : TailCofinalityBudgetUp} :
    tailCofinalityBudgetToEventFlow x = tailCofinalityBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      some x = some y := by
    calc
      some x =
          tailCofinalityBudgetFromEventFlow (tailCofinalityBudgetToEventFlow x) :=
            (TailCofinalityBudgetTasteGate_obligation_surface_round_trip x).symm
      _ = tailCofinalityBudgetFromEventFlow (tailCofinalityBudgetToEventFlow y) :=
            congrArg tailCofinalityBudgetFromEventFlow heq
      _ = some y := TailCofinalityBudgetTasteGate_obligation_surface_round_trip y
  exact Option.some.inj hread

instance tailCofinalityBudgetBHistCarrier : BHistCarrier TailCofinalityBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailCofinalityBudgetToEventFlow
  fromEventFlow := tailCofinalityBudgetFromEventFlow

instance tailCofinalityBudgetChapterTasteGate :
    ChapterTasteGate TailCofinalityBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := TailCofinalityBudgetTasteGate_obligation_surface_round_trip
  layer_separation := by
    intro x y hneq hflow
    exact hneq (TailCofinalityBudgetTasteGate_obligation_surface_injective hflow)

instance tailCofinalityBudgetFieldFaithful :
    FieldFaithful TailCofinalityBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tailCofinalityBudgetFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk threshold₁ window₁ dyadic₁ readback₁ sealRow₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk threshold₂ window₂ dyadic₂ readback₂ sealRow₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hThreshold t1
            injection t1 with hWindow t2
            injection t2 with hDyadic t3
            injection t3 with hReadback t4
            injection t4 with hSeal t5
            injection t5 with hTransport t6
            injection t6 with hRoute t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hThreshold
            cases hWindow
            cases hDyadic
            cases hReadback
            cases hSeal
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

instance tailCofinalityBudgetNontrivial :
    Nontrivial TailCofinalityBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TailCofinalityBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TailCofinalityBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TailCofinalityBudgetTasteGate_obligation_surface :
    Nonempty (Nontrivial TailCofinalityBudgetUp) ∧
      Nonempty (ChapterTasteGate TailCofinalityBudgetUp) ∧
        Nonempty (FieldFaithful TailCofinalityBudgetUp) ∧
          tailCofinalityBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact ⟨tailCofinalityBudgetNontrivial⟩
  · constructor
    · exact ⟨tailCofinalityBudgetChapterTasteGate⟩
    · constructor
      · exact ⟨tailCofinalityBudgetFieldFaithful⟩
      · rfl

def taste_gate : ChapterTasteGate TailCofinalityBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tailCofinalityBudgetChapterTasteGate

end BEDC.Derived.TailCofinalityBudgetUp
