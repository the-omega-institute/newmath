import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySealFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySealFunctorUp : Type where
  | mk :
      (limitSeal targetClassifier transport window regular dyadic hsameRow route provenance
        name : BHist) →
      CauchySealFunctorUp
  deriving DecidableEq

def cauchySealFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySealFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySealFunctorEncodeBHist h

def cauchySealFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySealFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySealFunctorDecodeBHist tail)

private theorem cauchySealFunctorDecodeEncodeBHist :
    ∀ h : BHist, cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySealFunctorFields : CauchySealFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySealFunctorUp.mk limitSeal targetClassifier transport window regular dyadic
      hsameRow route provenance name =>
      [limitSeal, targetClassifier, transport, window, regular, dyadic, hsameRow, route,
        provenance, name]

def cauchySealFunctorToEventFlow : CauchySealFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySealFunctorFields x).map cauchySealFunctorEncodeBHist

def cauchySealFunctorFromEventFlow : EventFlow → Option CauchySealFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | limitSeal :: rest0 =>
      match rest0 with
      | [] => none
      | targetClassifier :: rest1 =>
          match rest1 with
          | [] => none
          | transport :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | hsameRow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchySealFunctorUp.mk
                                                  (cauchySealFunctorDecodeBHist limitSeal)
                                                  (cauchySealFunctorDecodeBHist
                                                    targetClassifier)
                                                  (cauchySealFunctorDecodeBHist transport)
                                                  (cauchySealFunctorDecodeBHist window)
                                                  (cauchySealFunctorDecodeBHist regular)
                                                  (cauchySealFunctorDecodeBHist dyadic)
                                                  (cauchySealFunctorDecodeBHist hsameRow)
                                                  (cauchySealFunctorDecodeBHist route)
                                                  (cauchySealFunctorDecodeBHist provenance)
                                                  (cauchySealFunctorDecodeBHist name))
                                          | _ :: _ => none

private theorem cauchySealFunctor_round_trip :
    ∀ x : CauchySealFunctorUp,
      cauchySealFunctorFromEventFlow (cauchySealFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk limitSeal targetClassifier transport window regular dyadic hsameRow route provenance
      name =>
      change
        some
          (CauchySealFunctorUp.mk
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist limitSeal))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist targetClassifier))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist transport))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist window))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist regular))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist dyadic))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist hsameRow))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist route))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist provenance))
            (cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist name))) =
          some
            (CauchySealFunctorUp.mk limitSeal targetClassifier transport window regular dyadic
              hsameRow route provenance name)
      rw [cauchySealFunctorDecodeEncodeBHist limitSeal,
        cauchySealFunctorDecodeEncodeBHist targetClassifier,
        cauchySealFunctorDecodeEncodeBHist transport,
        cauchySealFunctorDecodeEncodeBHist window,
        cauchySealFunctorDecodeEncodeBHist regular,
        cauchySealFunctorDecodeEncodeBHist dyadic,
        cauchySealFunctorDecodeEncodeBHist hsameRow,
        cauchySealFunctorDecodeEncodeBHist route,
        cauchySealFunctorDecodeEncodeBHist provenance,
        cauchySealFunctorDecodeEncodeBHist name]

private theorem cauchySealFunctorToEventFlow_injective {x y : CauchySealFunctorUp} :
    cauchySealFunctorToEventFlow x = cauchySealFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySealFunctorFromEventFlow (cauchySealFunctorToEventFlow x) =
        cauchySealFunctorFromEventFlow (cauchySealFunctorToEventFlow y) :=
    congrArg cauchySealFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySealFunctor_round_trip x).symm
      (Eq.trans hread (cauchySealFunctor_round_trip y)))

private theorem cauchySealFunctor_fields_faithful :
    ∀ x y : CauchySealFunctorUp, cauchySealFunctorFields x = cauchySealFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk limit₁ target₁ transport₁ window₁ regular₁ dyadic₁ hsame₁ route₁ provenance₁
      name₁ =>
      cases y with
      | mk limit₂ target₂ transport₂ window₂ regular₂ dyadic₂ hsame₂ route₂ provenance₂
          name₂ =>
          injection hfields with hlimit tail0
          injection tail0 with htarget tail1
          injection tail1 with htransport tail2
          injection tail2 with hwindow tail3
          injection tail3 with hregular tail4
          injection tail4 with hdyadic tail5
          injection tail5 with hhsame tail6
          injection tail6 with hroute tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hname _
          subst hlimit
          subst htarget
          subst htransport
          subst hwindow
          subst hregular
          subst hdyadic
          subst hhsame
          subst hroute
          subst hprovenance
          subst hname
          rfl

instance cauchySealFunctorBHistCarrier : BHistCarrier CauchySealFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySealFunctorToEventFlow
  fromEventFlow := cauchySealFunctorFromEventFlow

instance cauchySealFunctorChapterTasteGate : ChapterTasteGate CauchySealFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySealFunctorFromEventFlow (cauchySealFunctorToEventFlow x) = some x
    exact cauchySealFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySealFunctorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySealFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySealFunctorFromEventFlow (cauchySealFunctorToEventFlow x) = some x
    exact cauchySealFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySealFunctorToEventFlow_injective heq)

instance cauchySealFunctorFieldFaithful : FieldFaithful CauchySealFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySealFunctorFields
  field_faithful := cauchySealFunctor_fields_faithful

instance cauchySealFunctorNontrivial : Nontrivial CauchySealFunctorUp where
  witness_pair :=
    ⟨CauchySealFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySealFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem CauchySealFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySealFunctorDecodeBHist (cauchySealFunctorEncodeBHist h) = h) ∧
      (∀ x : CauchySealFunctorUp,
        cauchySealFunctorFromEventFlow (cauchySealFunctorToEventFlow x) = some x) ∧
        (∀ x y : CauchySealFunctorUp,
          cauchySealFunctorToEventFlow x = cauchySealFunctorToEventFlow y → x = y) ∧
          cauchySealFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchySealFunctorDecodeEncodeBHist
  · constructor
    · exact cauchySealFunctor_round_trip
    · constructor
      · intro x y heq
        exact cauchySealFunctorToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchySealFunctorUp
