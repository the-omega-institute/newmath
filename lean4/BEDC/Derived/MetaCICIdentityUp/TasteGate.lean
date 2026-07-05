import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICIdentityUp : Type where
  | mk :
      (generators equality recursors purity boundary transport routes provenance nameCert :
        BHist) →
      MetaCICIdentityUp
  deriving DecidableEq

def metaCICIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICIdentityEncodeBHist h

def metaCICIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICIdentityDecodeBHist tail)

private theorem metaCICIdentity_decode_encode_bhist :
    ∀ h : BHist, metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICIdentityFields : MetaCICIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
      provenance nameCert =>
      [generators, equality, recursors, purity, boundary, transport, routes, provenance,
        nameCert]

def metaCICIdentityToEventFlow : MetaCICIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICIdentityFields x).map metaCICIdentityEncodeBHist

def metaCICIdentityFromEventFlow : EventFlow → Option MetaCICIdentityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | generators :: rest0 =>
      match rest0 with
      | [] => none
      | equality :: rest1 =>
          match rest1 with
          | [] => none
          | recursors :: rest2 =>
              match rest2 with
              | [] => none
              | purity :: rest3 =>
                  match rest3 with
                  | [] => none
                  | boundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routes :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (MetaCICIdentityUp.mk
                                              (metaCICIdentityDecodeBHist generators)
                                              (metaCICIdentityDecodeBHist equality)
                                              (metaCICIdentityDecodeBHist recursors)
                                              (metaCICIdentityDecodeBHist purity)
                                              (metaCICIdentityDecodeBHist boundary)
                                              (metaCICIdentityDecodeBHist transport)
                                              (metaCICIdentityDecodeBHist routes)
                                              (metaCICIdentityDecodeBHist provenance)
                                              (metaCICIdentityDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem metaCICIdentity_round_trip :
    ∀ x : MetaCICIdentityUp,
      metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generators equality recursors purity boundary transport routes provenance nameCert =>
      change
        some
          (MetaCICIdentityUp.mk
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist generators))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist equality))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist recursors))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist purity))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist boundary))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist transport))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist routes))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist provenance))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist nameCert))) =
          some
            (MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
              provenance nameCert)
      rw [metaCICIdentity_decode_encode_bhist generators,
        metaCICIdentity_decode_encode_bhist equality,
        metaCICIdentity_decode_encode_bhist recursors,
        metaCICIdentity_decode_encode_bhist purity,
        metaCICIdentity_decode_encode_bhist boundary,
        metaCICIdentity_decode_encode_bhist transport,
        metaCICIdentity_decode_encode_bhist routes,
        metaCICIdentity_decode_encode_bhist provenance,
        metaCICIdentity_decode_encode_bhist nameCert]

private theorem metaCICIdentityToEventFlow_injective {x y : MetaCICIdentityUp} :
    metaCICIdentityToEventFlow x = metaCICIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) =
        metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow y) :=
    congrArg metaCICIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICIdentity_round_trip x).symm
      (Eq.trans hread (metaCICIdentity_round_trip y)))

private theorem metaCICIdentity_fields_faithful :
    ∀ x y : MetaCICIdentityUp, metaCICIdentityFields x = metaCICIdentityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk generators₁ equality₁ recursors₁ purity₁ boundary₁ transport₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk generators₂ equality₂ recursors₂ purity₂ boundary₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          injection hfields with hGenerators tail0
          injection tail0 with hEquality tail1
          injection tail1 with hRecursors tail2
          injection tail2 with hPurity tail3
          injection tail3 with hBoundary tail4
          injection tail4 with hTransport tail5
          injection tail5 with hRoutes tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hNameCert _
          subst hGenerators
          subst hEquality
          subst hRecursors
          subst hPurity
          subst hBoundary
          subst hTransport
          subst hRoutes
          subst hProvenance
          subst hNameCert
          rfl

instance metaCICIdentityBHistCarrier : BHistCarrier MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICIdentityToEventFlow
  fromEventFlow := metaCICIdentityFromEventFlow

instance metaCICIdentityChapterTasteGate :
    ChapterTasteGate MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x
    exact metaCICIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICIdentityToEventFlow_injective heq)

instance metaCICIdentityFieldFaithful : FieldFaithful MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICIdentityFields
  field_faithful := metaCICIdentity_fields_faithful

def taste_gate : ChapterTasteGate MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x
    exact metaCICIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICIdentityToEventFlow_injective heq)

theorem MetaCICIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist h) = h) ∧
      (∀ x : MetaCICIdentityUp,
        metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x) ∧
        (∀ x y : MetaCICIdentityUp,
          metaCICIdentityToEventFlow x = metaCICIdentityToEventFlow y -> x = y) ∧
          metaCICIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICIdentity_decode_encode_bhist
  · constructor
    · exact metaCICIdentity_round_trip
    · constructor
      · intro x y heq
        exact metaCICIdentityToEventFlow_injective heq
      · rfl

theorem MetaCICIdentity_namecert_obligations
    {generators equality recursors purity boundary transport routes provenance nameCert consumer
      readback : BHist} :
    UnaryHistory boundary ->
      UnaryHistory consumer ->
        Cont boundary consumer readback ->
          metaCICIdentityFields
              (MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
                provenance nameCert) =
            [generators, equality, recursors, purity, boundary, transport, routes, provenance,
              nameCert] ∧
            UnaryHistory readback ∧
              Cont boundary consumer readback ∧
                metaCICIdentityFromEventFlow
                    (metaCICIdentityToEventFlow
                      (MetaCICIdentityUp.mk generators equality recursors purity boundary transport
                        routes provenance nameCert)) =
                  some
                    (MetaCICIdentityUp.mk generators equality recursors purity boundary transport
                      routes provenance nameCert) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro unaryBoundary unaryConsumer boundaryRead
  constructor
  · rfl
  · constructor
    · exact unary_cont_closed unaryBoundary unaryConsumer boundaryRead
    · constructor
      · exact boundaryRead
      · exact
          metaCICIdentity_round_trip
            (MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
              provenance nameCert)

theorem MetaCICIdentity_boundary_nonescape
    {generators equality recursors purity boundary transport routes provenance nameCert consumer :
      BHist}
    (unaryBoundary : UnaryHistory boundary) (unaryConsumer : UnaryHistory consumer) :
    ∃ readback : BHist,
      Cont boundary consumer readback ∧
        UnaryHistory readback ∧
          metaCICIdentityFromEventFlow
              (metaCICIdentityToEventFlow
                (MetaCICIdentityUp.mk generators equality recursors purity boundary transport
                  routes provenance nameCert)) =
            some
              (MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
                provenance nameCert) ∧
            SemanticNameCert
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun row : BHist => hsame row boundary ∨ hsame row readback)
              (fun row : BHist => UnaryHistory row ∧ Cont boundary consumer readback)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  let readback : BHist := append boundary consumer
  have boundaryRead : Cont boundary consumer readback := rfl
  have unaryReadback : UnaryHistory readback :=
    unary_cont_closed unaryBoundary unaryConsumer boundaryRead
  have sourceReadback :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback :=
    ⟨hsame_refl readback, unaryReadback⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row readback ∧ UnaryHistory row)
        (fun row : BHist => hsame row boundary ∨ hsame row readback)
        (fun row : BHist => UnaryHistory row ∧ Cont boundary consumer readback)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceReadback
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRead⟩
  }
  exact
    ⟨readback, boundaryRead, unaryReadback,
      metaCICIdentity_round_trip
        (MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
          provenance nameCert),
      cert⟩

theorem MetaCICIdentity_generator_recursor_coverage
    {G E R A B H C P N recursorRead namedRead : BHist} :
    UnaryHistory G -> UnaryHistory R -> UnaryHistory H -> UnaryHistory C ->
      Cont G R recursorRead -> Cont H C namedRead ->
        metaCICIdentityFields (MetaCICIdentityUp.mk G E R A B H C P N) =
            [G, E, R, A, B, H, C, P, N] ∧
          UnaryHistory recursorRead ∧ UnaryHistory namedRead ∧
            hsame recursorRead (append G R) ∧ hsame namedRead (append H C) ∧
              metaCICIdentityFromEventFlow
                  (metaCICIdentityToEventFlow (MetaCICIdentityUp.mk G E R A B H C P N)) =
                some (MetaCICIdentityUp.mk G E R A B H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory MetaCICIdentityUp
  intro generatorUnary recursorUnary transportUnary routeUnary recursorRoute namedRoute
  have recursorReadUnary : UnaryHistory recursorRead :=
    unary_cont_closed generatorUnary recursorUnary recursorRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed transportUnary routeUnary namedRoute
  have sameRecursorRead : hsame recursorRead (append G R) := recursorRoute
  have sameNamedRead : hsame namedRead (append H C) := namedRoute
  exact
    ⟨rfl, recursorReadUnary, namedReadUnary, sameRecursorRead, sameNamedRead,
      metaCICIdentity_round_trip (MetaCICIdentityUp.mk G E R A B H C P N)⟩

theorem MetaCICIdentity_comparison_secondary
    {G E R A B H C P N comparisonRead diagnosticRead : BHist} :
    UnaryHistory G -> UnaryHistory B -> UnaryHistory P -> UnaryHistory N ->
      Cont G B comparisonRead -> Cont P N diagnosticRead ->
        metaCICIdentityFields (MetaCICIdentityUp.mk G E R A B H C P N) =
            [G, E, R, A, B, H, C, P, N] ∧
          UnaryHistory comparisonRead ∧ UnaryHistory diagnosticRead ∧
            hsame comparisonRead (append G B) ∧ hsame diagnosticRead (append P N) ∧
              metaCICIdentityFromEventFlow
                  (metaCICIdentityToEventFlow (MetaCICIdentityUp.mk G E R A B H C P N)) =
                some (MetaCICIdentityUp.mk G E R A B H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory MetaCICIdentityUp
  intro generatorUnary boundaryUnary provenanceUnary nameUnary comparisonRoute diagnosticRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed generatorUnary boundaryUnary comparisonRoute
  have diagnosticUnary : UnaryHistory diagnosticRead :=
    unary_cont_closed provenanceUnary nameUnary diagnosticRoute
  exact
    ⟨rfl, comparisonUnary, diagnosticUnary, comparisonRoute, diagnosticRoute,
      metaCICIdentity_round_trip (MetaCICIdentityUp.mk G E R A B H C P N)⟩

theorem MetaCICIdentity_obligation_boundary
    {G E R A B H C P N recursorRead comparisonRead diagnosticRead namedRead : BHist} :
    UnaryHistory G -> UnaryHistory R -> UnaryHistory B -> UnaryHistory H ->
      UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        Cont G R recursorRead -> Cont G B comparisonRead ->
          Cont P N diagnosticRead -> Cont H C namedRead ->
            metaCICIdentityFields (MetaCICIdentityUp.mk G E R A B H C P N) =
                [G, E, R, A, B, H, C, P, N] ∧
              UnaryHistory recursorRead ∧
                UnaryHistory comparisonRead ∧
                  UnaryHistory diagnosticRead ∧
                    UnaryHistory namedRead ∧
                      hsame recursorRead (append G R) ∧
                        hsame comparisonRead (append G B) ∧
                          hsame diagnosticRead (append P N) ∧
                            hsame namedRead (append H C) ∧
                              metaCICIdentityFromEventFlow
                                  (metaCICIdentityToEventFlow
                                    (MetaCICIdentityUp.mk G E R A B H C P N)) =
                                some (MetaCICIdentityUp.mk G E R A B H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory MetaCICIdentityUp
  intro generatorUnary recursorUnary boundaryUnary transportUnary routeUnary provenanceUnary
    nameUnary recursorRoute comparisonRoute diagnosticRoute namedRoute
  have recursorReadUnary : UnaryHistory recursorRead :=
    unary_cont_closed generatorUnary recursorUnary recursorRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed generatorUnary boundaryUnary comparisonRoute
  have diagnosticReadUnary : UnaryHistory diagnosticRead :=
    unary_cont_closed provenanceUnary nameUnary diagnosticRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed transportUnary routeUnary namedRoute
  exact
    ⟨rfl, recursorReadUnary, comparisonReadUnary, diagnosticReadUnary, namedReadUnary,
      recursorRoute, comparisonRoute, diagnosticRoute, namedRoute,
      metaCICIdentity_round_trip (MetaCICIdentityUp.mk G E R A B H C P N)⟩

theorem MetaCICIdentity_audit_map_route
    {G E R A B H C P N auditRead compilerRead identityRead localRead : BHist} :
    UnaryHistory P -> UnaryHistory G -> UnaryHistory E -> UnaryHistory B ->
      UnaryHistory N -> Cont P G auditRead -> Cont auditRead E compilerRead ->
        Cont compilerRead B identityRead -> Cont P N localRead ->
          metaCICIdentityFields (MetaCICIdentityUp.mk G E R A B H C P N) =
              [G, E, R, A, B, H, C, P, N] ∧
            UnaryHistory auditRead ∧
              UnaryHistory compilerRead ∧
                UnaryHistory identityRead ∧
                  UnaryHistory localRead ∧
                    hsame auditRead (append P G) ∧
                      hsame compilerRead (append auditRead E) ∧
                        hsame identityRead (append compilerRead B) ∧
                          hsame localRead (append P N) ∧
                            metaCICIdentityFromEventFlow
                                (metaCICIdentityToEventFlow
                                  (MetaCICIdentityUp.mk G E R A B H C P N)) =
                              some (MetaCICIdentityUp.mk G E R A B H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory MetaCICIdentityUp
  intro provenanceUnary generatorUnary equalityUnary boundaryUnary nameUnary auditRoute
    compilerRoute identityRoute localRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed provenanceUnary generatorUnary auditRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed auditReadUnary equalityUnary compilerRoute
  have identityReadUnary : UnaryHistory identityRead :=
    unary_cont_closed compilerReadUnary boundaryUnary identityRoute
  have localReadUnary : UnaryHistory localRead :=
    unary_cont_closed provenanceUnary nameUnary localRoute
  exact
    ⟨rfl, auditReadUnary, compilerReadUnary, identityReadUnary, localReadUnary, auditRoute,
      compilerRoute, identityRoute, localRoute,
      metaCICIdentity_round_trip (MetaCICIdentityUp.mk G E R A B H C P N)⟩

end BEDC.Derived.MetaCICIdentityUp
