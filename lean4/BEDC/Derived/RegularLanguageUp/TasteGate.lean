import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularLanguageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularLanguageUp : Type where
  | mk :
      (alphabet states start accept transition word run endpoint transport routes provenance :
        BHist) →
      RegularLanguageUp
  deriving DecidableEq

def regularLanguageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularLanguageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularLanguageEncodeBHist h

def regularLanguageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularLanguageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularLanguageDecodeBHist tail)

private theorem regularLanguage_decode_encode_bhist :
    ∀ h : BHist, regularLanguageDecodeBHist (regularLanguageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularLanguageFields : RegularLanguageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularLanguageUp.mk alphabet states start accept transition word run endpoint transport
      routes provenance =>
      [alphabet, states, start, accept, transition, word, run, endpoint, transport, routes,
        provenance]

def regularLanguageToEventFlow : RegularLanguageUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularLanguageFields x).map regularLanguageEncodeBHist

def regularLanguageFromEventFlow : EventFlow → Option RegularLanguageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | alphabet :: rest0 =>
      match rest0 with
      | [] => none
      | states :: rest1 =>
          match rest1 with
          | [] => none
          | start :: rest2 =>
              match rest2 with
              | [] => none
              | accept :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transition :: rest4 =>
                      match rest4 with
                      | [] => none
                      | word :: rest5 =>
                          match rest5 with
                          | [] => none
                          | run :: rest6 =>
                              match rest6 with
                              | [] => none
                              | endpoint :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routes :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RegularLanguageUp.mk
                                                      (regularLanguageDecodeBHist alphabet)
                                                      (regularLanguageDecodeBHist states)
                                                      (regularLanguageDecodeBHist start)
                                                      (regularLanguageDecodeBHist accept)
                                                      (regularLanguageDecodeBHist transition)
                                                      (regularLanguageDecodeBHist word)
                                                      (regularLanguageDecodeBHist run)
                                                      (regularLanguageDecodeBHist endpoint)
                                                      (regularLanguageDecodeBHist transport)
                                                      (regularLanguageDecodeBHist routes)
                                                      (regularLanguageDecodeBHist provenance))
                                              | _ :: _ => none

private theorem regularLanguage_round_trip :
    ∀ x : RegularLanguageUp,
      regularLanguageFromEventFlow (regularLanguageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk alphabet states start accept transition word run endpoint transport routes provenance =>
      change
        some
          (RegularLanguageUp.mk
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist alphabet))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist states))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist start))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist accept))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist transition))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist word))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist run))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist endpoint))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist transport))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist routes))
            (regularLanguageDecodeBHist (regularLanguageEncodeBHist provenance))) =
          some
            (RegularLanguageUp.mk alphabet states start accept transition word run endpoint
              transport routes provenance)
      rw [regularLanguage_decode_encode_bhist alphabet,
        regularLanguage_decode_encode_bhist states,
        regularLanguage_decode_encode_bhist start,
        regularLanguage_decode_encode_bhist accept,
        regularLanguage_decode_encode_bhist transition,
        regularLanguage_decode_encode_bhist word,
        regularLanguage_decode_encode_bhist run,
        regularLanguage_decode_encode_bhist endpoint,
        regularLanguage_decode_encode_bhist transport,
        regularLanguage_decode_encode_bhist routes,
        regularLanguage_decode_encode_bhist provenance]

private theorem regularLanguageToEventFlow_injective {x y : RegularLanguageUp} :
    regularLanguageToEventFlow x = regularLanguageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = regularLanguageFromEventFlow (regularLanguageToEventFlow x) :=
        (regularLanguage_round_trip x).symm
      _ = regularLanguageFromEventFlow (regularLanguageToEventFlow y) :=
        congrArg regularLanguageFromEventFlow hxy
      _ = some y := regularLanguage_round_trip y
  exact Option.some.inj optionEq

instance regularLanguageBHistCarrier : BHistCarrier RegularLanguageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularLanguageToEventFlow
  fromEventFlow := regularLanguageFromEventFlow

instance regularLanguageChapterTasteGate : ChapterTasteGate RegularLanguageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularLanguageFromEventFlow (regularLanguageToEventFlow x) = some x
    exact regularLanguage_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularLanguageToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularLanguageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularLanguageChapterTasteGate

theorem RegularLanguageTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularLanguageDecodeBHist (regularLanguageEncodeBHist h) = h) ∧
      (∀ x : RegularLanguageUp,
        regularLanguageFromEventFlow (regularLanguageToEventFlow x) = some x) ∧
        (∀ x y : RegularLanguageUp,
          regularLanguageToEventFlow x = regularLanguageToEventFlow y → x = y) ∧
          regularLanguageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularLanguage_decode_encode_bhist,
      regularLanguage_round_trip,
      (by
        intro x y heq
        exact regularLanguageToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularLanguageUp
