import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionMonadUp : Type where
  | mk (source windows observations schedule diagonal sealRow ledger routes provenance name : BHist) :
      CauchyCompletionMonadUp
  deriving DecidableEq

def cauchyCompletionMonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionMonadEncodeBHist h

def cauchyCompletionMonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionMonadDecodeBHist tail)

private theorem cauchyCompletionMonad_decode_encode :
    ∀ h : BHist, cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionMonadFields : CauchyCompletionMonadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionMonadUp.mk source windows observations schedule diagonal sealRow ledger routes
      provenance name =>
      [source, windows, observations, schedule, diagonal, sealRow, ledger, routes, provenance, name]

def cauchyCompletionMonadToEventFlow : CauchyCompletionMonadUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCompletionMonadFields x).map cauchyCompletionMonadEncodeBHist

def cauchyCompletionMonadFromEventFlow : EventFlow → Option CauchyCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | source :: rest1 =>
        match rest1 with
        | [] => none
        | windows :: rest2 =>
            match rest2 with
            | [] => none
            | observations :: rest3 =>
                match rest3 with
                | [] => none
                | schedule :: rest4 =>
                    match rest4 with
                    | [] => none
                    | diagonal :: rest5 =>
                        match rest5 with
                        | [] => none
                        | sealRow :: rest6 =>
                            match rest6 with
                            | [] => none
                            | ledger :: rest7 =>
                                match rest7 with
                                | [] => none
                                | routes :: rest8 =>
                                    match rest8 with
                                    | [] => none
                                    | provenance :: rest9 =>
                                        match rest9 with
                                        | [] => none
                                        | name :: rest10 =>
                                            match rest10 with
                                            | [] =>
                                                some
                                                  (CauchyCompletionMonadUp.mk
                                                    (cauchyCompletionMonadDecodeBHist source)
                                                    (cauchyCompletionMonadDecodeBHist windows)
                                                    (cauchyCompletionMonadDecodeBHist observations)
                                                    (cauchyCompletionMonadDecodeBHist schedule)
                                                    (cauchyCompletionMonadDecodeBHist diagonal)
                                                    (cauchyCompletionMonadDecodeBHist sealRow)
                                                    (cauchyCompletionMonadDecodeBHist ledger)
                                                    (cauchyCompletionMonadDecodeBHist routes)
                                                    (cauchyCompletionMonadDecodeBHist provenance)
                                                    (cauchyCompletionMonadDecodeBHist name))
                                            | _ :: _ => none

private theorem cauchyCompletionMonad_round_trip :
    ∀ x : CauchyCompletionMonadUp,
      cauchyCompletionMonadFromEventFlow (cauchyCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source windows observations schedule diagonal sealRow ledger routes provenance name =>
      change
        some
            (CauchyCompletionMonadUp.mk
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist source))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist windows))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist observations))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist schedule))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist diagonal))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist sealRow))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist ledger))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist routes))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist provenance))
              (cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist name))) =
          some
            (CauchyCompletionMonadUp.mk source windows observations schedule diagonal sealRow
              ledger routes provenance name)
      rw [cauchyCompletionMonad_decode_encode source, cauchyCompletionMonad_decode_encode windows,
        cauchyCompletionMonad_decode_encode observations, cauchyCompletionMonad_decode_encode schedule,
        cauchyCompletionMonad_decode_encode diagonal, cauchyCompletionMonad_decode_encode sealRow,
        cauchyCompletionMonad_decode_encode ledger, cauchyCompletionMonad_decode_encode routes,
        cauchyCompletionMonad_decode_encode provenance, cauchyCompletionMonad_decode_encode name]

private theorem cauchyCompletionMonadToEventFlow_injective {x y : CauchyCompletionMonadUp} :
    cauchyCompletionMonadToEventFlow x = cauchyCompletionMonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionMonadFromEventFlow (cauchyCompletionMonadToEventFlow x) =
        cauchyCompletionMonadFromEventFlow (cauchyCompletionMonadToEventFlow y) :=
    congrArg cauchyCompletionMonadFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (cauchyCompletionMonad_round_trip x).symm
        (Eq.trans hread (cauchyCompletionMonad_round_trip y)))

private theorem cauchyCompletionMonad_fields_faithful :
    ∀ x y : CauchyCompletionMonadUp,
      cauchyCompletionMonadFields x = cauchyCompletionMonadFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source windows observations schedule diagonal sealRow ledger routes provenance name =>
      cases y with
      | mk source' windows' observations' schedule' diagonal' sealRow' ledger' routes'
          provenance' name' =>
          cases hfields
          rfl

instance cauchyCompletionMonadBHistCarrier : BHistCarrier CauchyCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionMonadToEventFlow
  fromEventFlow := cauchyCompletionMonadFromEventFlow

instance cauchyCompletionMonadChapterTasteGate :
    ChapterTasteGate CauchyCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionMonadFromEventFlow (cauchyCompletionMonadToEventFlow x) = some x
    exact cauchyCompletionMonad_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionMonadToEventFlow_injective heq)

instance cauchyCompletionMonadFieldFaithful : FieldFaithful CauchyCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionMonadFields
  field_faithful := cauchyCompletionMonad_fields_faithful

instance cauchyCompletionMonadNontrivial : Nontrivial CauchyCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionMonadUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionMonadUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionMonadChapterTasteGate

theorem CauchyCompletionMonadTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCompletionMonadDecodeBHist (cauchyCompletionMonadEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionMonadUp,
        cauchyCompletionMonadFromEventFlow (cauchyCompletionMonadToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionMonadUp,
          cauchyCompletionMonadToEventFlow x = cauchyCompletionMonadToEventFlow y → x = y) ∧
          cauchyCompletionMonadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact cauchyCompletionMonad_decode_encode
  · constructor
    · exact cauchyCompletionMonad_round_trip
    · constructor
      · intro x y heq
        exact cauchyCompletionMonadToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyCompletionMonadUp
