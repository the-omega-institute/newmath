import BEDC.Derived.DoCalculusUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoCalculusUp

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

inductive DoCalculusUp : Type where
  | mk :
      (intervention variables adjustment distribution independence expectation exported htrans
        replay provenance localName : BHist) →
        DoCalculusUp
  deriving DecidableEq

def doCalculusTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0, BMark.b1]

def doCalculusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doCalculusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doCalculusEncodeBHist h

def doCalculusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doCalculusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doCalculusDecodeBHist tail)

private theorem DoCalculusUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, doCalculusDecodeBHist (doCalculusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem DoCalculusUpTasteGate_single_carrier_alignment_mk_congr
    {intervention₁ variables₁ adjustment₁ distribution₁ independence₁ expectation₁ exported₁
      htrans₁ replay₁ provenance₁ localName₁ intervention₂ variables₂ adjustment₂ distribution₂
      independence₂ expectation₂ exported₂ htrans₂ replay₂ provenance₂ localName₂ : BHist} :
    intervention₁ = intervention₂ →
      variables₁ = variables₂ →
        adjustment₁ = adjustment₂ →
          distribution₁ = distribution₂ →
            independence₁ = independence₂ →
              expectation₁ = expectation₂ →
                exported₁ = exported₂ →
                  htrans₁ = htrans₂ →
                    replay₁ = replay₂ →
                      provenance₁ = provenance₂ →
                        localName₁ = localName₂ →
                          DoCalculusUp.mk intervention₁ variables₁ adjustment₁ distribution₁
                              independence₁ expectation₁ exported₁ htrans₁ replay₁ provenance₁
                              localName₁ =
                            DoCalculusUp.mk intervention₂ variables₂ adjustment₂ distribution₂
                              independence₂ expectation₂ exported₂ htrans₂ replay₂ provenance₂
                              localName₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hIntervention hVariables hAdjustment hDistribution hIndependence hExpectation hExported
    hHtrans hReplay hProvenance hLocalName
  cases hIntervention
  cases hVariables
  cases hAdjustment
  cases hDistribution
  cases hIndependence
  cases hExpectation
  cases hExported
  cases hHtrans
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def doCalculusFields : DoCalculusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoCalculusUp.mk intervention variables adjustment distribution independence expectation
      exported htrans replay provenance localName =>
      [intervention, variables, adjustment, distribution, independence, expectation, exported,
        htrans, replay, provenance, localName]

def doCalculusToEventFlow : DoCalculusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DoCalculusUp.mk intervention variables adjustment distribution independence expectation
      exported htrans replay provenance localName =>
      [doCalculusTag, doCalculusEncodeBHist intervention, doCalculusEncodeBHist variables,
        doCalculusEncodeBHist adjustment, doCalculusEncodeBHist distribution,
        doCalculusEncodeBHist independence, doCalculusEncodeBHist expectation,
        doCalculusEncodeBHist exported, doCalculusEncodeBHist htrans,
        doCalculusEncodeBHist replay, doCalculusEncodeBHist provenance,
        doCalculusEncodeBHist localName]

def doCalculusFromEventFlow : EventFlow → Option DoCalculusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | intervention :: rest1 =>
          match rest1 with
          | [] => none
          | variables :: rest2 =>
              match rest2 with
              | [] => none
              | adjustment :: rest3 =>
                  match rest3 with
                  | [] => none
                  | distribution :: rest4 =>
                      match rest4 with
                      | [] => none
                      | independence :: rest5 =>
                          match rest5 with
                          | [] => none
                          | expectation :: rest6 =>
                              match rest6 with
                              | [] => none
                              | exported :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | htrans :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (DoCalculusUp.mk
                                                          (doCalculusDecodeBHist
                                                            intervention)
                                                          (doCalculusDecodeBHist variables)
                                                          (doCalculusDecodeBHist adjustment)
                                                          (doCalculusDecodeBHist
                                                            distribution)
                                                          (doCalculusDecodeBHist
                                                            independence)
                                                          (doCalculusDecodeBHist
                                                            expectation)
                                                          (doCalculusDecodeBHist exported)
                                                          (doCalculusDecodeBHist htrans)
                                                          (doCalculusDecodeBHist replay)
                                                          (doCalculusDecodeBHist provenance)
                                                          (doCalculusDecodeBHist localName))
                                                  | _ :: _ => none

private theorem DoCalculusUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DoCalculusUp, doCalculusFromEventFlow (doCalculusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk intervention variables adjustment distribution independence expectation exported htrans
      replay provenance localName =>
      change
        some
          (DoCalculusUp.mk
            (doCalculusDecodeBHist (doCalculusEncodeBHist intervention))
            (doCalculusDecodeBHist (doCalculusEncodeBHist variables))
            (doCalculusDecodeBHist (doCalculusEncodeBHist adjustment))
            (doCalculusDecodeBHist (doCalculusEncodeBHist distribution))
            (doCalculusDecodeBHist (doCalculusEncodeBHist independence))
            (doCalculusDecodeBHist (doCalculusEncodeBHist expectation))
            (doCalculusDecodeBHist (doCalculusEncodeBHist exported))
            (doCalculusDecodeBHist (doCalculusEncodeBHist htrans))
            (doCalculusDecodeBHist (doCalculusEncodeBHist replay))
            (doCalculusDecodeBHist (doCalculusEncodeBHist provenance))
            (doCalculusDecodeBHist (doCalculusEncodeBHist localName))) =
          some
            (DoCalculusUp.mk intervention variables adjustment distribution independence
              expectation exported htrans replay provenance localName)
      exact congrArg some
        (DoCalculusUpTasteGate_single_carrier_alignment_mk_congr
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode intervention)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode variables)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode adjustment)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode distribution)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode independence)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode expectation)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode exported)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode htrans)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode replay)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode provenance)
          (DoCalculusUpTasteGate_single_carrier_alignment_decode_encode localName))

private theorem DoCalculusUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DoCalculusUp} :
    doCalculusToEventFlow x = doCalculusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doCalculusFromEventFlow (doCalculusToEventFlow x) =
        doCalculusFromEventFlow (doCalculusToEventFlow y) :=
    congrArg doCalculusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DoCalculusUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DoCalculusUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem DoCalculusUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DoCalculusUp, doCalculusFields x = doCalculusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk intervention₁ variables₁ adjustment₁ distribution₁ independence₁ expectation₁
      exported₁ htrans₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk intervention₂ variables₂ adjustment₂ distribution₂ independence₂ expectation₂
          exported₂ htrans₂ replay₂ provenance₂ localName₂ =>
          injection hfields with hIntervention tail0
          injection tail0 with hVariables tail1
          injection tail1 with hAdjustment tail2
          injection tail2 with hDistribution tail3
          injection tail3 with hIndependence tail4
          injection tail4 with hExpectation tail5
          injection tail5 with hExported tail6
          injection tail6 with hHtrans tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hIntervention
          subst hVariables
          subst hAdjustment
          subst hDistribution
          subst hIndependence
          subst hExpectation
          subst hExported
          subst hHtrans
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance DoCalculusUpTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DoCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doCalculusToEventFlow
  fromEventFlow := doCalculusFromEventFlow

instance DoCalculusUpTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DoCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doCalculusFromEventFlow (doCalculusToEventFlow x) = some x
    exact DoCalculusUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DoCalculusUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance DoCalculusUpTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful DoCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := doCalculusFields
  field_faithful := DoCalculusUpTasteGate_single_carrier_alignment_fields_faithful

instance DoCalculusUpTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial DoCalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DoCalculusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DoCalculusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DoCalculusUpTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DoCalculusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DoCalculusUpTasteGate_single_carrier_alignment_ChapterTasteGate

theorem DoCalculusUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, doCalculusDecodeBHist (doCalculusEncodeBHist h) = h) ∧
      (∀ x : DoCalculusUp, doCalculusFromEventFlow (doCalculusToEventFlow x) = some x) ∧
        (∀ x y : DoCalculusUp,
          doCalculusToEventFlow x = doCalculusToEventFlow y → x = y) ∧
          doCalculusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact DoCalculusUpTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact DoCalculusUpTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DoCalculusUpTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

theorem DoCalculusUpTasteGate_namecert_surface_eventflow_consumer [AskSetup] [PackageSetup]
    {intervention variables adjustment distribution independence expectation exported htrans replay
      provenance localName interventionRead adjustmentRead probabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoCalculusPacket intervention variables adjustment distribution independence expectation exported
        htrans replay provenance localName bundle pkg →
      Cont intervention variables interventionRead →
        Cont adjustment independence adjustmentRead →
          Cont expectation exported probabilityRead →
            PkgSig bundle localName pkg →
              let carrier :=
                DoCalculusUp.mk intervention variables adjustment distribution independence expectation
                  exported htrans replay provenance localName
              doCalculusFromEventFlow (doCalculusToEventFlow carrier) = some carrier ∧
                doCalculusFields carrier =
                  [intervention, variables, adjustment, distribution, independence, expectation,
                    exported, htrans, replay, provenance, localName] ∧
                  SemanticNameCert
                      (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row interventionRead ∨ hsame row adjustmentRead ∨
                          hsame row probabilityRead ∨ hsame row localName)
                      (fun row : BHist => PkgSig bundle localName pkg ∧ hsame row localName)
                      hsame ∧
                    UnaryHistory interventionRead ∧ UnaryHistory adjustmentRead ∧
                      UnaryHistory probabilityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert ChapterTasteGate
  intro packet interventionCont adjustmentCont probabilityCont localNamePkg
  let carrier :=
    DoCalculusUp.mk intervention variables adjustment distribution independence expectation exported
      htrans replay provenance localName
  have surface :=
    DoCalculusPacket_namecert_obligation_surface
      (interventionRead := interventionRead) (adjustmentRead := adjustmentRead)
      (probabilityRead := probabilityRead) packet interventionCont adjustmentCont probabilityCont
      localNamePkg
  exact ⟨DoCalculusUpTasteGate_single_carrier_alignment.right.left carrier, rfl, surface⟩

theorem DoCalculusUpTasteGate_adjustment_ledger_eventflow_consumer [AskSetup] [PackageSetup]
    {intervention variables adjustment distribution independence expectation exported htrans replay
      provenance localName adjustmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoCalculusPacket intervention variables adjustment distribution independence expectation exported
        htrans replay provenance localName bundle pkg →
      Cont adjustment independence adjustmentRead →
        PkgSig bundle adjustmentRead pkg →
          let carrier :=
            DoCalculusUp.mk intervention variables adjustment distribution independence expectation
              exported htrans replay provenance localName
          doCalculusFromEventFlow (doCalculusToEventFlow carrier) = some carrier ∧
            doCalculusFields carrier =
              [intervention, variables, adjustment, distribution, independence, expectation,
                exported, htrans, replay, provenance, localName] ∧
              UnaryHistory variables ∧ UnaryHistory adjustment ∧ UnaryHistory independence ∧
                UnaryHistory adjustmentRead ∧ Cont intervention variables adjustment ∧
                  Cont adjustment distribution independence ∧
                    Cont adjustment independence adjustmentRead ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle adjustmentRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont ChapterTasteGate
  intro packet adjustmentCont adjustmentPkg
  let carrier :=
    DoCalculusUp.mk intervention variables adjustment distribution independence expectation exported
      htrans replay provenance localName
  have ledger :=
    DoCalculusPacket_adjustment_ledger_exactness packet adjustmentCont adjustmentPkg
  exact ⟨DoCalculusUpTasteGate_single_carrier_alignment.right.left carrier, rfl, ledger⟩

end BEDC.Derived.DoCalculusUp
