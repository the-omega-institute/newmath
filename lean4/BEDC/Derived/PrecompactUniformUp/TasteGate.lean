import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrecompactUniformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrecompactUniformUp : Type where
  | mk :
      (source entourage cover comparison request completion window readback tolerance transport
        replay provenance name : BHist) →
      PrecompactUniformUp
  deriving DecidableEq

def precompactUniformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: precompactUniformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: precompactUniformEncodeBHist h

def precompactUniformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (precompactUniformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (precompactUniformDecodeBHist tail)

theorem PrecompactUniformTasteGate_decode :
    ∀ h : BHist, precompactUniformDecodeBHist (precompactUniformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def precompactUniformFields : PrecompactUniformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrecompactUniformUp.mk source entourage cover comparison request completion window readback
      tolerance transport replay provenance name =>
      [source, entourage, cover, comparison, request, completion, window, readback, tolerance,
        transport, replay, provenance, name]

theorem PrecompactUniformTasteGate_mk_congr
    {source source' entourage entourage' cover cover' comparison comparison' request request'
      completion completion' window window' readback readback' tolerance tolerance'
      transport transport' replay replay' provenance provenance' name name' : BHist}
    (hSource : source' = source)
    (hEntourage : entourage' = entourage)
    (hCover : cover' = cover)
    (hComparison : comparison' = comparison)
    (hRequest : request' = request)
    (hCompletion : completion' = completion)
    (hWindow : window' = window)
    (hReadback : readback' = readback)
    (hTolerance : tolerance' = tolerance)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    PrecompactUniformUp.mk source' entourage' cover' comparison' request' completion' window'
        readback' tolerance' transport' replay' provenance' name' =
      PrecompactUniformUp.mk source entourage cover comparison request completion window readback
        tolerance transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hEntourage
  cases hCover
  cases hComparison
  cases hRequest
  cases hCompletion
  cases hWindow
  cases hReadback
  cases hTolerance
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def precompactUniformToEventFlow : PrecompactUniformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PrecompactUniformUp.mk source entourage cover comparison request completion window readback
      tolerance transport replay provenance name =>
      [[BMark.b0],
        precompactUniformEncodeBHist source,
        [BMark.b1, BMark.b0],
        precompactUniformEncodeBHist entourage,
        [BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist cover,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist request,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist completion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        precompactUniformEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        precompactUniformEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        precompactUniformEncodeBHist name]

def precompactUniformFromEventFlow : EventFlow → Option PrecompactUniformUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | entourage :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cover :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | comparison :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | request :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | completion :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | window :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | readback :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | tolerance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] => none
                                                                              | transport ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | replay ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | provenance ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match
                                                                                                        rest24
                                                                                                      with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | name ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (PrecompactUniformUp.mk
                                                                                                                  (precompactUniformDecodeBHist source)
                                                                                                                  (precompactUniformDecodeBHist entourage)
                                                                                                                  (precompactUniformDecodeBHist cover)
                                                                                                                  (precompactUniformDecodeBHist comparison)
                                                                                                                  (precompactUniformDecodeBHist request)
                                                                                                                  (precompactUniformDecodeBHist completion)
                                                                                                                  (precompactUniformDecodeBHist window)
                                                                                                                  (precompactUniformDecodeBHist readback)
                                                                                                                  (precompactUniformDecodeBHist tolerance)
                                                                                                                  (precompactUniformDecodeBHist transport)
                                                                                                                  (precompactUniformDecodeBHist replay)
                                                                                                                  (precompactUniformDecodeBHist provenance)
                                                                                                                  (precompactUniformDecodeBHist name))
                                                                                                          | _ ::
                                                                                                              _ =>
                                                                                                              none

theorem PrecompactUniformTasteGate_round_trip :
    ∀ x : PrecompactUniformUp,
      precompactUniformFromEventFlow (precompactUniformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source entourage cover comparison request completion window readback tolerance transport
      replay provenance name =>
      exact
        congrArg some
          (PrecompactUniformTasteGate_mk_congr
            (PrecompactUniformTasteGate_decode source)
            (PrecompactUniformTasteGate_decode entourage)
            (PrecompactUniformTasteGate_decode cover)
            (PrecompactUniformTasteGate_decode comparison)
            (PrecompactUniformTasteGate_decode request)
            (PrecompactUniformTasteGate_decode completion)
            (PrecompactUniformTasteGate_decode window)
            (PrecompactUniformTasteGate_decode readback)
            (PrecompactUniformTasteGate_decode tolerance)
            (PrecompactUniformTasteGate_decode transport)
            (PrecompactUniformTasteGate_decode replay)
            (PrecompactUniformTasteGate_decode provenance)
            (PrecompactUniformTasteGate_decode name))

theorem PrecompactUniformTasteGate_injective {x y : PrecompactUniformUp} :
    precompactUniformToEventFlow x = precompactUniformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : some x = some y := by
    calc
      some x =
          precompactUniformFromEventFlow (precompactUniformToEventFlow x) :=
            (PrecompactUniformTasteGate_round_trip x).symm
      _ = precompactUniformFromEventFlow (precompactUniformToEventFlow y) :=
            congrArg precompactUniformFromEventFlow heq
      _ = some y := PrecompactUniformTasteGate_round_trip y
  exact Option.some.inj hread

instance precompactUniformBHistCarrier : BHistCarrier PrecompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := precompactUniformToEventFlow
  fromEventFlow := precompactUniformFromEventFlow

instance precompactUniformChapterTasteGate : ChapterTasteGate PrecompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := PrecompactUniformTasteGate_round_trip
  layer_separation := by
    intro x y hneq hflow
    exact hneq (PrecompactUniformTasteGate_injective hflow)

instance precompactUniformFieldFaithful : FieldFaithful PrecompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := precompactUniformFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk source₁ entourage₁ cover₁ comparison₁ request₁ completion₁ window₁ readback₁
        tolerance₁ transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk source₂ entourage₂ cover₂ comparison₂ request₂ completion₂ window₂ readback₂
            tolerance₂ transport₂ replay₂ provenance₂ name₂ =>
            injection h with hSource t1
            injection t1 with hEntourage t2
            injection t2 with hCover t3
            injection t3 with hComparison t4
            injection t4 with hRequest t5
            injection t5 with hCompletion t6
            injection t6 with hWindow t7
            injection t7 with hReadback t8
            injection t8 with hTolerance t9
            injection t9 with hTransport t10
            injection t10 with hReplay t11
            injection t11 with hProvenance t12
            injection t12 with hName _
            cases hSource
            cases hEntourage
            cases hCover
            cases hComparison
            cases hRequest
            cases hCompletion
            cases hWindow
            cases hReadback
            cases hTolerance
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

instance precompactUniformNontrivial : Nontrivial PrecompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrecompactUniformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PrecompactUniformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PrecompactUniformTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PrecompactUniformUp) ∧
      Nonempty (FieldFaithful PrecompactUniformUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial PrecompactUniformUp) ∧
          (∀ h : BHist, precompactUniformDecodeBHist (precompactUniformEncodeBHist h) = h) ∧
            precompactUniformEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨precompactUniformChapterTasteGate⟩
  · constructor
    · exact ⟨precompactUniformFieldFaithful⟩
    · constructor
      · exact ⟨precompactUniformNontrivial⟩
      · constructor
        · exact PrecompactUniformTasteGate_decode
        · rfl

def taste_gate : ChapterTasteGate PrecompactUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  precompactUniformChapterTasteGate

end BEDC.Derived.PrecompactUniformUp
