import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationAutomatonUp : Type where
  | mk (states initial accepting transitions behaviour transport routes provenance nameCert :
      BHist) : ContinuationAutomatonUp
  deriving DecidableEq

def continuationAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationAutomatonEncodeBHist h

def continuationAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationAutomatonDecodeBHist tail)

private theorem continuationAutomatonDecode_encode_bhist :
    ∀ h : BHist, continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def continuationAutomatonToEventFlow : ContinuationAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationAutomatonUp.mk states initial accepting transitions behaviour transport routes
      provenance nameCert =>
      [[BMark.b0],
        continuationAutomatonEncodeBHist states,
        [BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist initial,
        [BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist accepting,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist transitions,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist behaviour,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        continuationAutomatonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        continuationAutomatonEncodeBHist nameCert]

def continuationAutomatonFromEventFlow : EventFlow → Option ContinuationAutomatonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | states :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | initial :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | accepting :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transitions :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | behaviour :: rest9 =>
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
                                                      | routes :: rest13 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ContinuationAutomatonUp.mk
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    states)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    initial)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    accepting)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    transitions)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    behaviour)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    transport)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    routes)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    provenance)
                                                                                  (continuationAutomatonDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem continuationAutomaton_round_trip :
    ∀ x : ContinuationAutomatonUp,
      continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk states initial accepting transitions behaviour transport routes provenance nameCert =>
      change
        some
          (ContinuationAutomatonUp.mk
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist states))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist initial))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist accepting))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist transitions))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist behaviour))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist transport))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist routes))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist provenance))
            (continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist nameCert))) =
          some
            (ContinuationAutomatonUp.mk states initial accepting transitions behaviour transport
              routes provenance nameCert)
      rw [continuationAutomatonDecode_encode_bhist states,
        continuationAutomatonDecode_encode_bhist initial,
        continuationAutomatonDecode_encode_bhist accepting,
        continuationAutomatonDecode_encode_bhist transitions,
        continuationAutomatonDecode_encode_bhist behaviour,
        continuationAutomatonDecode_encode_bhist transport,
        continuationAutomatonDecode_encode_bhist routes,
        continuationAutomatonDecode_encode_bhist provenance,
        continuationAutomatonDecode_encode_bhist nameCert]

private theorem continuationAutomatonToEventFlow_injective {x y : ContinuationAutomatonUp} :
    continuationAutomatonToEventFlow x = continuationAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) =
        continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow y) :=
    congrArg continuationAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuationAutomaton_round_trip x).symm
      (Eq.trans hread (continuationAutomaton_round_trip y)))

instance continuationAutomatonBHistCarrier : BHistCarrier ContinuationAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationAutomatonToEventFlow
  fromEventFlow := continuationAutomatonFromEventFlow

instance continuationAutomatonChapterTasteGate : ChapterTasteGate ContinuationAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) = some x
    exact continuationAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationAutomatonToEventFlow_injective heq)

instance continuationAutomatonFieldFaithful : FieldFaithful ContinuationAutomatonUp where
  fields := fun x =>
    match x with
    | ContinuationAutomatonUp.mk states initial accepting transitions behaviour transport routes
        provenance nameCert =>
        [states, initial, accepting, transitions, behaviour, transport, routes, provenance,
          nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk states₁ initial₁ accepting₁ transitions₁ behaviour₁ transport₁ routes₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk states₂ initial₂ accepting₂ transitions₂ behaviour₂ transport₂ routes₂ provenance₂
            nameCert₂ =>
            injection h with hstates tail₁
            injection tail₁ with hinitial tail₂
            injection tail₂ with haccepting tail₃
            injection tail₃ with htransitions tail₄
            injection tail₄ with hbehaviour tail₅
            injection tail₅ with htransport tail₆
            injection tail₆ with hroutes tail₇
            injection tail₇ with hprovenance tail₈
            injection tail₈ with hnameCert _
            cases hstates
            cases hinitial
            cases haccepting
            cases htransitions
            cases hbehaviour
            cases htransport
            cases hroutes
            cases hprovenance
            cases hnameCert
            rfl

def taste_gate : ChapterTasteGate ContinuationAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationAutomatonChapterTasteGate

theorem ContinuationAutomatonTasteGate_single_carrier_alignment :
    (∀ h : BHist, continuationAutomatonDecodeBHist (continuationAutomatonEncodeBHist h) = h) ∧
      (∀ x : ContinuationAutomatonUp,
        continuationAutomatonFromEventFlow (continuationAutomatonToEventFlow x) = some x) ∧
        (∀ x y : ContinuationAutomatonUp,
          continuationAutomatonToEventFlow x = continuationAutomatonToEventFlow y → x = y) ∧
          continuationAutomatonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact continuationAutomatonDecode_encode_bhist
  · constructor
    · exact continuationAutomaton_round_trip
    · constructor
      · intro x y heq
        exact continuationAutomatonToEventFlow_injective heq
      · rfl

def ContinuationAutomatonCarrier [AskSetup] [PackageSetup]
    (states initial accepting transitions behaviour transport routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory states ∧ UnaryHistory initial ∧ UnaryHistory accepting ∧
    UnaryHistory transitions ∧ UnaryHistory behaviour ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont initial transitions behaviour ∧ Cont transitions routes provenance ∧
          Cont accepting behaviour transport ∧ Cont provenance nameCert states ∧
            PkgSig bundle nameCert pkg

theorem ContinuationAutomatonCarrier_behaviour_classifier_stability [AskSetup] [PackageSetup]
    {states initial accepting transitions behaviour transport routes provenance nameCert
      behaviourRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationAutomatonCarrier states initial accepting transitions behaviour transport routes
        provenance nameCert bundle pkg ->
      hsame behaviourRead behaviour ->
        SemanticNameCert
          (fun row : BHist =>
            ContinuationAutomatonCarrier states initial accepting transitions behaviour transport
              routes provenance nameCert bundle pkg ∧ hsame row behaviour)
          (fun row : BHist =>
            Cont initial transitions behaviour ∧ hsame row behaviour ∧
              PkgSig bundle nameCert pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle nameCert pkg) hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier sameRead
  have carrierWitness := carrier
  obtain ⟨_statesUnary, _initialUnary, _acceptingUnary, _transitionsUnary, behaviourUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    initialTransitionsBehaviour, _transitionsRoutesProvenance, _acceptingBehaviourTransport,
    _provenanceNameStates, namePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro behaviourRead (And.intro carrierWitness sameRead)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact And.intro initialTransitionsBehaviour (And.intro source.right namePkg)
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport behaviourUnary (hsame_symm source.right)
      exact And.intro rowUnary namePkg
  }

theorem ContinuationAutomatonCarrier_acceptance_nonescape [AskSetup] [PackageSetup]
    {states initial accepting transitions behaviour transport routes provenance nameCert
      acceptingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationAutomatonCarrier states initial accepting transitions behaviour transport routes
        provenance nameCert bundle pkg ->
      Cont accepting behaviour acceptingRead ->
        UnaryHistory acceptingRead ∧ UnaryHistory accepting ∧ UnaryHistory behaviour ∧
          Cont accepting behaviour transport ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier acceptingBehaviourRead
  obtain ⟨_statesUnary, _initialUnary, acceptingUnary, _transitionsUnary, behaviourUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _initialTransitionsBehaviour, _transitionsRoutesProvenance, acceptingBehaviourTransport,
    _provenanceNameStates, namePkg⟩ := carrier
  have acceptingReadUnary : UnaryHistory acceptingRead :=
    unary_cont_closed acceptingUnary behaviourUnary acceptingBehaviourRead
  exact
    ⟨acceptingReadUnary, acceptingUnary, behaviourUnary, acceptingBehaviourTransport, namePkg⟩

end BEDC.Derived.ContinuationAutomatonUp
