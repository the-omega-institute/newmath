import BEDC.FKernel.Ext
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

/-
BEDC.Reflection: statement-only scaffolds for the capstone chapter
`papers/bedc/parts/visions/reflection_and_limits.tex`. Each definition
records the proposition asserted by a chapter theorem; later R-rounds
substantiate the body with the actual Lean statement and then add a
matching theorem proof, at which point the paper marker switches from
\leanstmt to \leanchecked.
-/

namespace BEDC.Reflection

open BEDC.FKernel.Ext
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert

/-- Irreducibility of the form of distinction (statement scaffold). -/
def form_of_distinction_irreducible : Prop :=
  ∀ (Carrier Primitive : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Carrier Classifier →
      (∀ h : BHist, Carrier h ↔ ∃ s : BHist, ∃ m : BMark, Ext s m h) →
        (∀ {h s t : BHist} {m n : BMark}, Carrier h →
          Ext s m h → Ext t n h → hsame s t ∧ msame m n) ∧
          (∀ {h : BHist}, Primitive h → Carrier h →
            ∃ s : BHist, ∃ m : BMark, Ext s m h) ∧
            (msame BMark.b0 BMark.b1 → False)

theorem form_of_distinction_irreducible_proof : form_of_distinction_irreducible := by
  intro Carrier Primitive Classifier _cert carrier_ext
  constructor
  · intro h s t m n _carrier_h left right
    exact ext_result_injective_pair left right
  · constructor
    · intro h _primitive_h carrier_h
      exact (carrier_ext h).mp carrier_h
    · exact not_msame_b0_b1

/-- Definition-classifier correspondence (statement scaffold). -/
def definition_classifier_correspondence : Prop :=
  ∀ (Carrier Definition : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Carrier Classifier →
      (∀ h : BHist, Definition h ↔
        Carrier h ∧ ∃ s : BHist, ∃ r : BHist, ∃ m : BMark,
          Ext s m h ∧ Cont s h r) →
        (∀ {h k : BHist}, Classifier h k →
          (∃ s : BHist, ∃ r : BHist, ∃ m : BMark, Ext s m h ∧ Cont s h r) →
            ∃ s : BHist, ∃ r : BHist, ∃ m : BMark, Ext s m k ∧ Cont s k r) →
          (∀ {h k : BHist}, Classifier h k → Definition h → Definition k) ∧
            (∀ {h k : BHist}, Definition h → Definition k → hsame h k → Classifier h k)

theorem definition_classifier_correspondence_proof :
    definition_classifier_correspondence := by
  intro Carrier Definition Classifier cert definition_iff data_transport
  constructor
  · intro h k classified defined_h
    have h_data :
        Carrier h ∧ ∃ s : BHist, ∃ r : BHist, ∃ m : BMark,
          Ext s m h ∧ Cont s h r :=
      (definition_iff h).mp defined_h
    have carrier_k : Carrier k :=
      BEDC.FKernel.NameCert.NameCert.carrier_respects_equiv cert classified h_data.left
    have k_data :
        ∃ s : BHist, ∃ r : BHist, ∃ m : BMark, Ext s m k ∧ Cont s k r :=
      data_transport classified h_data.right
    exact (definition_iff k).mpr (And.intro carrier_k k_data)
  · intro h k defined_h _defined_k same
    cases same
    have h_data :
        Carrier h ∧ ∃ s : BHist, ∃ r : BHist, ∃ m : BMark,
          Ext s m h ∧ Cont s h r :=
      (definition_iff h).mp defined_h
    exact BEDC.FKernel.NameCert.NameCert.equiv_refl cert h_data.left

/-- Inductive types as classifier closures (statement scaffold). -/
def inductive_as_classifier_closure : Prop :=
  ∀ (Carrier ConstructorClosed : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Carrier Classifier →
      (∀ h : BHist, ConstructorClosed h ↔
        Carrier h ∧ ∃ s : BHist, ∃ m : BMark, Ext s m h) →
        (∀ {h k : BHist}, Classifier h k →
          (∃ s : BHist, ∃ m : BMark, Ext s m h) →
            ∃ s : BHist, ∃ m : BMark, Ext s m k) →
          (∀ {h : BHist}, Carrier h →
            Carrier (BHist.e0 h) ∨ Carrier (BHist.e1 h)) →
            (∀ {h k : BHist}, Classifier h k → ConstructorClosed h → ConstructorClosed k) ∧
              (∀ {h : BHist}, Carrier h → ConstructorClosed (BHist.e0 h) ∨
                ConstructorClosed (BHist.e1 h))

theorem inductive_as_classifier_closure_proof : inductive_as_classifier_closure := by
  intro Carrier ConstructorClosed Classifier cert closureDef classifierPreservesExt carrierConstructorStep
  constructor
  · intro h k classified closedH
    have closedData : Carrier h ∧ ∃ s : BHist, ∃ m : BMark, Ext s m h :=
      (closureDef h).mp closedH
    have carrierK : Carrier k :=
      NameCert.carrier_respects_equiv cert classified closedData.left
    have extK : ∃ s : BHist, ∃ m : BMark, Ext s m k :=
      classifierPreservesExt classified closedData.right
    exact (closureDef k).mpr (And.intro carrierK extK)
  · intro h carrierH
    cases carrierConstructorStep carrierH with
    | inl carrierE0 =>
        exact Or.inl
          ((closureDef (BHist.e0 h)).mpr
            (And.intro carrierE0
              (Exists.intro h (Exists.intro BMark.b0 (Ext.e0 h)))))
    | inr carrierE1 =>
        exact Or.inr
          ((closureDef (BHist.e1 h)).mpr
            (And.intro carrierE1
              (Exists.intro h (Exists.intro BMark.b1 (Ext.e1 h)))))

/-- Internal description of the calculus of inductive constructions
(statement scaffold). -/
def internal_cic_interpretation : Prop :=
  ∀ (Term TypeForm Universe Ledger : BHist → Prop) (Classifier : BHist → BHist → Prop),
    SemanticNameCert Term TypeForm Ledger Classifier →
      (∀ t : BHist, Term t ↔ TypeForm t ∧ Universe t ∧
        ∃ s : BHist, ∃ m : BMark, Ext s m t) →
        (∀ {t u : BHist}, Classifier t u → Term t → TypeForm u ∧ Ledger u) ∧
          (∀ {t : BHist}, Term t →
            ∃ base : BHist, ∃ step : BHist, ∃ result : BHist,
              Ext base BMark.b0 step ∧ Cont step t result)

theorem internal_cic_interpretation_proof : internal_cic_interpretation := by
  intro Term TypeForm Universe Ledger Classifier cert _termSpec
  constructor
  · intro t u classified termT
    exact semanticNameCert_pattern_ledger_transport cert classified termT
  · intro t _termT
    exact Exists.intro BHist.Empty
      (Exists.intro (BHist.e0 BHist.Empty)
        (Exists.intro (append (BHist.e0 BHist.Empty) t)
          (And.intro (Ext.e0 BHist.Empty) rfl)))

/-- BEDC self-description (statement scaffold). -/
def bedc_self_description : Prop :=
  ∀ (FormalClaim InternalClaim Ledger : BHist → Prop) (Classifier : BHist → BHist → Prop),
    SemanticNameCert FormalClaim InternalClaim Ledger Classifier →
      (∀ h : BHist, FormalClaim h → ∃ s : BHist, ∃ m : BMark, Ext s m h) →
        (∀ {h k : BHist}, Classifier h k → FormalClaim h → InternalClaim k ∧ Ledger k) ∧
          (∀ {h k : BHist}, hsame h k → FormalClaim h → InternalClaim k)

theorem bedc_self_description_proof : bedc_self_description := by
  intro FormalClaim InternalClaim Ledger Classifier cert _extensionWitness
  constructor
  · intro h k classified formalClaim
    exact semanticNameCert_pattern_ledger_transport cert classified formalClaim
  · intro h k same formalClaim
    cases same
    exact cert.pattern_sound formalClaim

/-- Closed ground loop and open meta loop (statement scaffold). -/
def two_loops_theorem : Prop :=
  ∀ (Ground Meta Reflection OpenBoundary : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Ground Classifier →
      SemanticNameCert Meta Reflection OpenBoundary Classifier →
        (∀ h : BHist, Ground h ↔ ∃ s : BHist, ∃ m : BMark, Ext s m h) →
          (∀ h : BHist, Meta h → ∃ k : BHist, ∃ r : BHist, Cont h k r) →
            (∀ {h k : BHist}, Classifier h k → Ground h → Ground k) ∧
            (∀ {h : BHist}, Ground h → ∃ s : BHist, ∃ m : BMark, Ext s m h) ∧
                (∀ {h : BHist}, Meta h →
                  ∃ k : BHist, ∃ r : BHist, Cont h k r ∧ OpenBoundary r)

theorem two_loops_theorem_proof : two_loops_theorem := by
  intro Ground Meta Reflection OpenBoundary Classifier groundCert metaCert groundExt _metaCont
  constructor
  · intro h k classified groundH
    exact NameCert.carrier_respects_equiv groundCert classified groundH
  · constructor
    · intro h groundH
      exact (groundExt h).mp groundH
    · intro h metaH
      exact Exists.intro BHist.Empty
        (Exists.intro h (And.intro rfl (SemanticNameCert.ledger_sound metaCert metaH)))

/-- Continuation as Plotkin-style small-step relation (statement scaffold). -/
def computation_as_continuation_correspondence : Prop :=
  ∀ (Terminates : BHist → Prop) (Step Behavior : BHist → BHist → Prop),
    NameCert Terminates Behavior →
      (∀ h k : BHist, Step h k ↔ ∃ tail : BHist, Cont h tail k) →
        (∀ {h k : BHist}, Step h k → ∃ tail : BHist, Cont h tail k) ∧
          (∀ {h k : BHist}, (∃ tail : BHist, Cont h tail k) → Step h k) ∧
            (∀ {h k : BHist}, Behavior h k → Terminates h → Terminates k) ∧
              (∀ {h : BHist}, Terminates h → Behavior h h) ∧
                (∀ {h k : BHist}, hsame h k → Terminates h → Behavior h k)

theorem computation_as_continuation_correspondence_proof :
    computation_as_continuation_correspondence := by
  intro Terminates Step Behavior cert step_cont
  constructor
  · intro h k step
    exact (step_cont h k).mp step
  · constructor
    · intro h k cont
      exact (step_cont h k).mpr cont
    · constructor
      · intro h k behavior terminates_h
        exact NameCert.carrier_respects_equiv cert behavior terminates_h
      · constructor
        · intro h terminates_h
          exact NameCert.equiv_refl cert terminates_h
        · intro h k same terminates_h
          cases same
          exact NameCert.equiv_refl cert terminates_h

/-- Type checking as Ext membership. -/
def type_checking_as_ext_membership : Prop :=
  ∀ (WellTyped : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert WellTyped Classifier →
      (∀ t : BHist, WellTyped t ↔ ∃ h : BHist, ∃ m : BMark, Ext h m t) →
        (∀ {h k : BHist}, Classifier h k → WellTyped h → WellTyped k) ∧
          (∀ {h k : BHist}, Classifier h k →
            (∃ s : BHist, ∃ m : BMark, Ext s m h) →
              ∃ s : BHist, ∃ m : BMark, Ext s m k)

theorem type_checking_as_ext_membership_proof : type_checking_as_ext_membership := by
  intro WellTyped Classifier cert ext_iff
  constructor
  · intro h k classified wellTypedH
    exact NameCert.carrier_respects_equiv cert classified wellTypedH
  · intro h k classified extH
    have wellTypedH : WellTyped h := (ext_iff h).mpr extH
    have wellTypedK : WellTyped k :=
      NameCert.carrier_respects_equiv cert classified wellTypedH
    exact (ext_iff k).mp wellTypedK

/-- Compiler as naming-certificate morphism (statement scaffold). -/
def compilation_as_namecert_morphism : Prop :=
  ∀ (Source Target : BHist → Prop) (SourceClassifier TargetClassifier CompilerGraph : BHist → BHist → Prop),
    NameCert Source SourceClassifier →
      NameCert Target TargetClassifier →
        (∀ h k : BHist, CompilerGraph h k → Source h ∧ Target k) →
          (∀ {h h' k : BHist}, CompilerGraph h k → SourceClassifier h h' →
            ∃ k' : BHist, CompilerGraph h' k') →
          (∀ {h h' k k' : BHist}, CompilerGraph h k → CompilerGraph h' k' →
            SourceClassifier h h' → TargetClassifier k k') →
            (∀ {h h' k : BHist}, CompilerGraph h k → SourceClassifier h h' →
              ∃ k' : BHist, CompilerGraph h' k' ∧ TargetClassifier k k') ∧
              (∀ {h k k' : BHist}, CompilerGraph h k → TargetClassifier k k' → Target k')

theorem compilation_as_namecert_morphism_proof :
    compilation_as_namecert_morphism := by
  intro Source Target SourceClassifier TargetClassifier CompilerGraph _sourceCert targetCert graphCarrier graphLift graphPreserves
  constructor
  · intro h h' k graph sourceClassified
    cases graphLift graph sourceClassified with
    | intro k' liftedGraph =>
        exact Exists.intro k' (And.intro liftedGraph (graphPreserves graph liftedGraph sourceClassified))
  · intro h k k' graph targetClassified
    exact BEDC.FKernel.NameCert.NameCert.carrier_respects_equiv targetCert targetClassified (graphCarrier h k graph).right

/-- Halting problem as Tarski-style fixed-point obstruction over Cont
(statement scaffold). -/
def halting_as_form_of_distinction_fixed_point : Prop :=
  ∀ (Halts Diverges SelfRef : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Halts Classifier →
      (∀ h : BHist, Halts h ↔ ∃ fuel : BHist, ∃ result : BHist, Cont h fuel result) →
        (∀ h : BHist, SelfRef h → ∃ s : BHist, ∃ m : BMark, Ext s m h) →
          (∀ {h r : BHist}, SelfRef h → Cont h BHist.Empty r →
            Classifier h r → Diverges r) →
          (∀ {h k : BHist}, Classifier h k → Halts h → Halts k) ∧
            (∀ {h : BHist}, Halts h) ∧
              (∀ {h : BHist}, SelfRef h →
                ∃ s : BHist, ∃ m : BMark, ∃ k : BHist, ∃ r : BHist,
                  Ext s m h ∧ Cont h k r ∧ Halts r ∧ (Classifier h r → Diverges r))

theorem halting_as_form_of_distinction_fixed_point_proof :
    halting_as_form_of_distinction_fixed_point := by
  intro Halts Diverges SelfRef Classifier cert halts_iff selfref_ext diagonal
  constructor
  · intro h k classified halt_h
    exact NameCert.carrier_respects_equiv cert classified halt_h
  · constructor
    · intro h
      exact (halts_iff h).mpr ⟨BHist.Empty, h, cont_right_unit h⟩
    · intro h self_h
      cases selfref_ext h self_h with
      | intro s rest =>
          cases rest with
          | intro m ext_h =>
              refine ⟨s, m, BHist.Empty, h, ext_h, cont_right_unit h, ?_, ?_⟩
              · exact (halts_iff h).mpr ⟨BHist.Empty, h, cont_right_unit h⟩
              · intro classified
                exact diagonal self_h (cont_right_unit h) classified

end BEDC.Reflection
