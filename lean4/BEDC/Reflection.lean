import BEDC.FKernel.Ext
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

/-
BEDC.Reflection: statement-only scaffolds for the capstone chapter
`papers/bedc/parts/capstones/reflection_and_limits.tex`. Each definition
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

/-- Definition-classifier correspondence (statement scaffold). -/
def definition_classifier_correspondence : Prop :=
  ∀ (Carrier Definition : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Carrier Classifier →
      (∀ h : BHist, Definition h ↔
        Carrier h ∧ ∃ s : BHist, ∃ r : BHist, ∃ m : BMark,
          Ext s m h ∧ Cont s h r) →
        (∀ {h k : BHist}, Classifier h k → Definition h → Definition k) ∧
          (∀ {h k : BHist}, Definition h → Definition k → hsame h k → Classifier h k)

/-- Inductive types as classifier closures (statement scaffold). -/
def inductive_as_classifier_closure : Prop :=
  ∀ (Carrier ConstructorClosed : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Carrier Classifier →
      (∀ h : BHist, ConstructorClosed h ↔
        Carrier h ∧ ∃ s : BHist, ∃ m : BMark, Ext s m h) →
        (∀ {h k : BHist}, Classifier h k → ConstructorClosed h → ConstructorClosed k) ∧
          (∀ {h : BHist}, Carrier h → ConstructorClosed (BHist.e0 h) ∨
            ConstructorClosed (BHist.e1 h))

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

/-- BEDC self-description (statement scaffold). -/
def bedc_self_description : Prop :=
  ∀ (FormalClaim InternalClaim Ledger : BHist → Prop) (Classifier : BHist → BHist → Prop),
    SemanticNameCert FormalClaim InternalClaim Ledger Classifier →
      (∀ h : BHist, FormalClaim h → ∃ s : BHist, ∃ m : BMark, Ext s m h) →
        (∀ {h k : BHist}, Classifier h k → FormalClaim h → InternalClaim k ∧ Ledger k) ∧
          (∀ {h k : BHist}, hsame h k → FormalClaim h → InternalClaim k)

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

/-- Continuation as Plotkin-style small-step relation (statement scaffold). -/
def computation_as_continuation_correspondence : Prop :=
  ∀ (Terminates : BHist → Prop) (Step Behavior : BHist → BHist → Prop),
    NameCert Terminates Behavior →
      (∀ h k : BHist, Step h k ↔ ∃ tail : BHist, Cont h tail k) →
        (∀ {h k : BHist}, Step h k → ∃ tail : BHist, Cont h tail k) ∧
          (∀ {h k : BHist}, Behavior h k → Terminates h → Terminates k) ∧
            (∀ {h k : BHist}, hsame h k → Behavior h k)

/-- Type checking as Ext membership. -/
def type_checking_as_ext_membership : Prop :=
  ∀ (WellTyped : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert WellTyped Classifier →
      (∀ t : BHist, WellTyped t ↔ ∃ h : BHist, ∃ m : BMark, Ext h m t) →
        (∀ {h k : BHist}, Classifier h k → WellTyped h → WellTyped k) ∧
          (∀ {h k : BHist}, Classifier h k →
            (∃ s : BHist, ∃ m : BMark, Ext s m h) →
              ∃ s : BHist, ∃ m : BMark, Ext s m k)

/-- Compiler as naming-certificate morphism (statement scaffold). -/
def compilation_as_namecert_morphism : Prop :=
  ∀ (Source Target : BHist → Prop) (SourceClassifier TargetClassifier CompilerGraph : BHist → BHist → Prop),
    NameCert Source SourceClassifier →
      NameCert Target TargetClassifier →
        (∀ h k : BHist, CompilerGraph h k → Source h ∧ Target k) →
          (∀ {h h' k k' : BHist}, CompilerGraph h k → CompilerGraph h' k' →
            SourceClassifier h h' → TargetClassifier k k') →
            (∀ {h h' k : BHist}, CompilerGraph h k → SourceClassifier h h' →
              ∃ k' : BHist, CompilerGraph h' k' ∧ TargetClassifier k k') ∧
              (∀ {h k k' : BHist}, CompilerGraph h k → TargetClassifier k k' → Target k')

/-- Halting problem as Tarski-style fixed-point obstruction over Cont
(statement scaffold). -/
def halting_as_form_of_distinction_fixed_point : Prop :=
  ∀ (Halts Diverges SelfRef : BHist → Prop) (Classifier : BHist → BHist → Prop),
    NameCert Halts Classifier →
      (∀ h : BHist, Halts h ↔ ∃ fuel : BHist, ∃ result : BHist, Cont h fuel result) →
        (∀ h : BHist, SelfRef h → ∃ s : BHist, ∃ m : BMark, Ext s m h) →
          (∀ {h k : BHist}, Classifier h k → Halts h → Halts k) ∧
            (∀ {h : BHist}, SelfRef h → Halts h → Diverges h → False) ∧
              (∀ {h : BHist}, SelfRef h →
                ∃ k : BHist, ∃ r : BHist, Cont h k r ∧ (Classifier h r → Diverges r))

end BEDC.Reflection
