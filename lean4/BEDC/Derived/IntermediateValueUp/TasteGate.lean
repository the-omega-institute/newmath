import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ask
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntermediateValueUp : Type where
  | mk :
      (locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
        bisectionLedger nestedWindow realSeal transports routes provenance localNameCert :
          BHist) →
        IntermediateValueUp
  deriving DecidableEq

def IntermediateValueTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b0, BMark.b1]

def IntermediateValueTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: IntermediateValueTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: IntermediateValueTasteGate_single_carrier_alignment_encodeBHist h

def IntermediateValueTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem IntermediateValueTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
          (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def IntermediateValueTasteGate_single_carrier_alignment_fields :
    IntermediateValueUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueUp.mk locatedInterval endpointNegative endpointPositive continuousMap
      modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
      localNameCert =>
      [locatedInterval, endpointNegative, endpointPositive, continuousMap, modulusBudget,
        bisectionLedger, nestedWindow, realSeal, transports, routes, provenance,
        localNameCert]

def IntermediateValueTasteGate_single_carrier_alignment_toEventFlow :
    IntermediateValueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueUp.mk locatedInterval endpointNegative endpointPositive continuousMap
      modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
      localNameCert =>
      [IntermediateValueTasteGate_single_carrier_alignment_tag,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist locatedInterval,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist endpointNegative,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist endpointPositive,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist continuousMap,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist modulusBudget,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist bisectionLedger,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist nestedWindow,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist realSeal,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist transports,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist routes,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist provenance,
        IntermediateValueTasteGate_single_carrier_alignment_encodeBHist localNameCert]

def IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option IntermediateValueUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tag :: rest0 =>
      match tag with
      | [BMark.b1, BMark.b0, BMark.b0, BMark.b1] =>
          match rest0 with
          | [] => none
          | locatedInterval :: rest1 =>
              match rest1 with
              | [] => none
              | endpointNegative :: rest2 =>
                  match rest2 with
                  | [] => none
                  | endpointPositive :: rest3 =>
                      match rest3 with
                      | [] => none
                      | continuousMap :: rest4 =>
                          match rest4 with
                          | [] => none
                          | modulusBudget :: rest5 =>
                              match rest5 with
                              | [] => none
                              | bisectionLedger :: rest6 =>
                                  match rest6 with
                                  | [] => none
                                  | nestedWindow :: rest7 =>
                                      match rest7 with
                                      | [] => none
                                      | realSeal :: rest8 =>
                                          match rest8 with
                                          | [] => none
                                          | transports :: rest9 =>
                                              match rest9 with
                                              | [] => none
                                              | routes :: rest10 =>
                                                  match rest10 with
                                                  | [] => none
                                                  | provenance :: rest11 =>
                                                      match rest11 with
                                                      | [] => none
                                                      | localNameCert :: rest12 =>
                                                          match rest12 with
                                                          | [] =>
                                                              some
                                                                (IntermediateValueUp.mk
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    locatedInterval)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    endpointNegative)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    endpointPositive)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    continuousMap)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    modulusBudget)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    bisectionLedger)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    nestedWindow)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    realSeal)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    transports)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    routes)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    provenance)
                                                                  (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
                                                                    localNameCert))
                                                          | _ :: _ => none
      | _ => none

private theorem IntermediateValueTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntermediateValueUp,
      IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow
          (IntermediateValueTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert =>
      change
        some
          (IntermediateValueUp.mk
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist locatedInterval))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist endpointNegative))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist endpointPositive))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist continuousMap))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist modulusBudget))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist bisectionLedger))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist nestedWindow))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist realSeal))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist transports))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist routes))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist provenance))
            (IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist localNameCert))) =
          some
            (IntermediateValueUp.mk locatedInterval endpointNegative endpointPositive continuousMap
              modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
              localNameCert)
      rw [IntermediateValueTasteGate_single_carrier_alignment_decode_encode locatedInterval,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode endpointNegative,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode endpointPositive,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode continuousMap,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode modulusBudget,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode bisectionLedger,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode nestedWindow,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode realSeal,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode transports,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode routes,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode provenance,
        IntermediateValueTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem IntermediateValueTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntermediateValueUp} :
    IntermediateValueTasteGate_single_carrier_alignment_toEventFlow x =
        IntermediateValueTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow
          (IntermediateValueTasteGate_single_carrier_alignment_toEventFlow x) =
        IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow
          (IntermediateValueTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntermediateValueTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntermediateValueTasteGate_single_carrier_alignment_round_trip y)))

private theorem IntermediateValueTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : IntermediateValueUp,
      IntermediateValueTasteGate_single_carrier_alignment_fields x =
          IntermediateValueTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk locatedInterval₁ endpointNegative₁ endpointPositive₁ continuousMap₁ modulusBudget₁
      bisectionLedger₁ nestedWindow₁ realSeal₁ transports₁ routes₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk locatedInterval₂ endpointNegative₂ endpointPositive₂ continuousMap₂ modulusBudget₂
          bisectionLedger₂ nestedWindow₂ realSeal₂ transports₂ routes₂ provenance₂
          localNameCert₂ =>
          injection hfields with hLocatedInterval tail0
          injection tail0 with hEndpointNegative tail1
          injection tail1 with hEndpointPositive tail2
          injection tail2 with hContinuousMap tail3
          injection tail3 with hModulusBudget tail4
          injection tail4 with hBisectionLedger tail5
          injection tail5 with hNestedWindow tail6
          injection tail6 with hRealSeal tail7
          injection tail7 with hTransports tail8
          injection tail8 with hRoutes tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hLocalNameCert _
          subst hLocatedInterval
          subst hEndpointNegative
          subst hEndpointPositive
          subst hContinuousMap
          subst hModulusBudget
          subst hBisectionLedger
          subst hNestedWindow
          subst hRealSeal
          subst hTransports
          subst hRoutes
          subst hProvenance
          subst hLocalNameCert
          rfl

instance IntermediateValueTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier IntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := IntermediateValueTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow

instance IntermediateValueTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate IntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      IntermediateValueTasteGate_single_carrier_alignment_fromEventFlow
          (IntermediateValueTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact IntermediateValueTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntermediateValueTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance IntermediateValueTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful IntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := IntermediateValueTasteGate_single_carrier_alignment_fields
  field_faithful := IntermediateValueTasteGate_single_carrier_alignment_fields_faithful

instance IntermediateValueTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial IntermediateValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntermediateValueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntermediateValueUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def IntermediateValueTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate IntermediateValueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  IntermediateValueTasteGate_single_carrier_alignment_ChapterTasteGate

theorem IntermediateValueTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      IntermediateValueTasteGate_single_carrier_alignment_decodeBHist
          (IntermediateValueTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      IntermediateValueTasteGate_single_carrier_alignment_fields
          (IntermediateValueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        IntermediateValueTasteGate_single_carrier_alignment_toEventFlow
            (IntermediateValueUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty) =
          [[BMark.b1, BMark.b0, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [], [], [],
            [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact IntermediateValueTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

theorem IntermediateValueCarrier_dyadic_bisection_obligations
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert :
        BHist} :
    SemanticNameCert (fun row : BHist => hsame row realSeal)
        (fun row : BHist => hsame row realSeal)
        (fun row : BHist => hsame row realSeal) hsame ∧
      IntermediateValueTasteGate_single_carrier_alignment_fields
          (IntermediateValueUp.mk locatedInterval endpointNegative endpointPositive continuousMap
            modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
            localNameCert) =
        [locatedInterval, endpointNegative, endpointPositive, continuousMap, modulusBudget,
          bisectionLedger, nestedWindow, realSeal, transports, routes, provenance,
          localNameCert] := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro realSeal (hsame_refl realSeal)
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
          intro _row _row' sameRows sourceRow
          exact hsame_trans (hsame_symm sameRows) sourceRow
      }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow
      ledger_sound := by
        intro _row sourceRow
        exact sourceRow
    }
  · rfl

def IntermediateValueCarrier [AskSetup] [PackageSetup]
    (locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory locatedInterval ∧ UnaryHistory endpointNegative ∧
    UnaryHistory endpointPositive ∧ UnaryHistory continuousMap ∧
      UnaryHistory modulusBudget ∧ UnaryHistory bisectionLedger ∧
        UnaryHistory transports ∧ UnaryHistory routes ∧
          UnaryHistory provenance ∧ UnaryHistory localNameCert ∧
            Cont modulusBudget bisectionLedger nestedWindow ∧
              Cont bisectionLedger nestedWindow realSeal ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg

theorem IntermediateValueBisectionConvergenceHandoff [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      bisectionRead streamRead regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont bisectionLedger nestedWindow bisectionRead →
      Cont bisectionRead routes streamRead →
        Cont streamRead regseqRead realRead →
          PkgSig bundle realRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row realRead ∧ Cont bisectionLedger nestedWindow bisectionRead)
                (fun row : BHist =>
                  hsame row realRead ∧ Cont bisectionLedger nestedWindow bisectionRead ∧
                    Cont bisectionRead routes streamRead ∧
                      Cont streamRead regseqRead realRead)
                (fun row : BHist => hsame row realRead ∧ PkgSig bundle realRead pkg)
                hsame ∧
              hsame realRead realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro ledgerWindow routeStream streamRegseq realPkg
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realRead (And.intro (hsame_refl realRead) ledgerWindow)
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
          intro _row _row' sameRows sourceRow
          exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            sourceRow.right
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, sourceRow.right, routeStream, streamRegseq⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, realPkg⟩
    }
  · exact hsame_refl realRead

theorem IntermediateValueCarrier_bisection_convergence_handoff [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget bisectionLedger
      nestedWindow realSeal transports routes provenance localNameCert bisectionSeal consumer :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont nestedWindow provenance bisectionSeal ->
        Cont bisectionSeal localNameCert consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory nestedWindow ∧ UnaryHistory bisectionSeal ∧
              UnaryHistory consumer ∧ Cont bisectionLedger nestedWindow realSeal ∧
                Cont nestedWindow provenance bisectionSeal ∧
                  Cont bisectionSeal localNameCert consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier convergenceRoute consumerRoute consumerPkg
  obtain ⟨_locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, provenanceUnary,
    localNameCertUnary, modulusBisectionNested, bisectionLedgerRoute, _provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have bisectionSealUnary : UnaryHistory bisectionSeal :=
    unary_cont_result_closed
      (And.intro nestedUnary (And.intro provenanceUnary convergenceRoute))
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_result_closed
      (And.intro bisectionSealUnary (And.intro localNameCertUnary consumerRoute))
  exact
    And.intro nestedUnary
      (And.intro bisectionSealUnary
        (And.intro consumerUnary
          (And.intro bisectionLedgerRoute
            (And.intro convergenceRoute (And.intro consumerRoute consumerPkg)))))

theorem IntermediateValueCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row endpointNegative ∨
              hsame row endpointPositive ∨ hsame row continuousMap ∨
                hsame row modulusBudget ∨ hsame row bisectionLedger ∨
                  hsame row nestedWindow ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row endpointNegative ∨
              hsame row endpointPositive ∨ hsame row continuousMap ∨
                hsame row modulusBudget ∨ hsame row bisectionLedger ∨
                  hsame row nestedWindow ∨ hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg ∧
              (hsame row locatedInterval ∨ hsame row endpointNegative ∨
                hsame row endpointPositive ∨ hsame row continuousMap ∨
                  hsame row modulusBudget ∨ hsame row bisectionLedger ∨
                    hsame row nestedWindow ∨ hsame row realSeal))
          hsame ∧
        UnaryHistory nestedWindow ∧ UnaryHistory realSeal ∧
          Cont modulusBudget bisectionLedger nestedWindow ∧
            Cont bisectionLedger nestedWindow realSeal ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory Cont
  intro carrier
  obtain ⟨_locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedReal, provenancePkg,
    localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedReal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row endpointNegative ∨
              hsame row endpointPositive ∨ hsame row continuousMap ∨
                hsame row modulusBudget ∨ hsame row bisectionLedger ∨
                  hsame row nestedWindow ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row endpointNegative ∨
              hsame row endpointPositive ∨ hsame row continuousMap ∨
                hsame row modulusBudget ∨ hsame row bisectionLedger ∨
                  hsame row nestedWindow ∨ hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg ∧
              (hsame row locatedInterval ∨ hsame row endpointNegative ∨
                hsame row endpointPositive ∨ hsame row continuousMap ∨
                  hsame row modulusBudget ∨ hsame row bisectionLedger ∨
                    hsame row nestedWindow ∨ hsame row realSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedInterval (Or.inl (hsame_refl locatedInterval))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases source with
        | inl sameLocated =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameLocated)
        | inr rest =>
            cases rest with
            | inl sameNegative =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNegative))
            | inr rest =>
                cases rest with
                | inl samePositive =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) samePositive)))
                | inr rest =>
                    cases rest with
                    | inl sameMap =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameMap))))
                    | inr rest =>
                        cases rest with
                        | inl sameModulus =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameModulus)))))
                        | inr rest =>
                            cases rest with
                            | inl sameBisection =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameBisection))))))
                            | inr rest =>
                                cases rest with
                                | inl sameNested =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameNested)))))))
                                | inr sameReal =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameReal)))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNameCertPkg, source⟩
  }
  exact
    ⟨cert, nestedUnary, realSealUnary, modulusBisectionNested, bisectionNestedReal,
      provenancePkg, localNameCertPkg⟩

end BEDC.Derived.IntermediateValueUp
