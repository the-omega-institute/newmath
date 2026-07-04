set_option maxHeartbeats 2000000

/-!
# Tannakian finite detector reduction

Scope: this file records the finite detector step for the Yang-Mills /
Langlands route.  The global analytic and Tannakian obligations are explicit
parameters; they are not discharged here.  The checked content is the
mechanical reduction from equality of all declared finite trace readouts to
equality of the semisimple class, together with a concrete finite table whose
detectors separate its classes.
-/

namespace BEDC.Derived.Visions

inductive YmLangTfdClass where
  | scalar
  | split
  | anisotropic

inductive YmLangTfdDetector where
  | standardTrace
  | determinantTrace

def ymLangTfdDetectorList : List YmLangTfdDetector :=
  [YmLangTfdDetector.standardTrace, YmLangTfdDetector.determinantTrace]

def ymLangTfdTrace : YmLangTfdDetector -> YmLangTfdClass -> Nat
  | .standardTrace, .scalar => 2
  | .standardTrace, .split => 0
  | .standardTrace, .anisotropic => 1
  | .determinantTrace, .scalar => 1
  | .determinantTrace, .split => 1
  | .determinantTrace, .anisotropic => 0

def ymLangTfdTraceVector (g : YmLangTfdClass) : List Nat :=
  ymLangTfdDetectorList.map (fun detector => ymLangTfdTrace detector g)

def ymLangTfdSameFiniteReadout
    (g h : YmLangTfdClass) : Prop :=
  ∀ detector : YmLangTfdDetector,
    ymLangTfdTrace detector g = ymLangTfdTrace detector h

def ymLangTfdTraceSameBool
    (detector : YmLangTfdDetector)
    (g h : YmLangTfdClass) : Bool :=
  Nat.beq (ymLangTfdTrace detector g) (ymLangTfdTrace detector h)

structure YmLangTfdSameFiniteReadoutCert
    (g h : YmLangTfdClass) : Type where
  standardTrace :
    ymLangTfdTraceSameBool YmLangTfdDetector.standardTrace g h = true
  determinantTrace :
    ymLangTfdTraceSameBool YmLangTfdDetector.determinantTrace g h = true

theorem ymLangTfd_nat_beq_true_of_eq
    {a b : Nat}
    (same : a = b) :
    Nat.beq a b = true := by
  cases same
  induction a with
  | zero => rfl
  | succ n ih => exact ih

def YmLangTfdSameFiniteReadoutCert.ofReadout
    {g h : YmLangTfdClass}
    (same : ymLangTfdSameFiniteReadout g h) :
    YmLangTfdSameFiniteReadoutCert g h where
  standardTrace :=
    ymLangTfd_nat_beq_true_of_eq
      (same YmLangTfdDetector.standardTrace)
  determinantTrace :=
    ymLangTfd_nat_beq_true_of_eq
      (same YmLangTfdDetector.determinantTrace)

theorem ymLangTfd_trace_vector_scalar :
    ymLangTfdTraceVector YmLangTfdClass.scalar = [2, 1] := by
  rfl

theorem ymLangTfd_trace_vector_split :
    ymLangTfdTraceVector YmLangTfdClass.split = [0, 1] := by
  rfl

theorem ymLangTfd_trace_vector_anisotropic :
    ymLangTfdTraceVector YmLangTfdClass.anisotropic = [1, 0] := by
  rfl

theorem ymLangTfd_finite_detector_cert_separates_classes :
    ∀ g h : YmLangTfdClass,
      YmLangTfdSameFiniteReadoutCert g h -> g = h
  | .scalar, .scalar, _same => rfl
  | .scalar, .split, same => by
      cases same.standardTrace
  | .scalar, .anisotropic, same => by
      cases same.standardTrace
  | .split, .scalar, same => by
      cases same.standardTrace
  | .split, .split, _same => rfl
  | .split, .anisotropic, same => by
      cases same.standardTrace
  | .anisotropic, .scalar, same => by
      cases same.standardTrace
  | .anisotropic, .split, same => by
      cases same.standardTrace
  | .anisotropic, .anisotropic, _same => rfl

theorem ymLangTfd_finite_detectors_separate_classes
    (g h : YmLangTfdClass)
    (same : ymLangTfdSameFiniteReadout g h) :
    g = h :=
  ymLangTfd_finite_detector_cert_separates_classes
    g h (YmLangTfdSameFiniteReadoutCert.ofReadout same)

structure YmLangTfdConditionalObligations
    (Class Detector TraceValue : Type) where
  trace : Detector -> Class -> TraceValue
  separates_semisimple_classes :
    ∀ {g h : Class},
      (∀ detector : Detector, trace detector g = trace detector h) -> g = h

def ymLangTfdSameConditionalReadout
    {Class Detector TraceValue : Type}
    (obligations :
      YmLangTfdConditionalObligations Class Detector TraceValue)
    (g h : Class) : Prop :=
  ∀ detector : Detector,
    obligations.trace detector g = obligations.trace detector h

theorem ymLangTfd_conditional_tannakian_reduction
    {Class Detector TraceValue : Type}
    (obligations :
      YmLangTfdConditionalObligations Class Detector TraceValue)
    {g h : Class}
    (same :
      ymLangTfdSameConditionalReadout obligations g h) :
    g = h :=
  obligations.separates_semisimple_classes same

def ymLangTfdFiniteObligations :
    YmLangTfdConditionalObligations
      YmLangTfdClass YmLangTfdDetector Nat where
  trace := ymLangTfdTrace
  separates_semisimple_classes := by
    intro g h same
    exact ymLangTfd_finite_detectors_separate_classes g h same

theorem ymLangTfd_finite_table_reduces_to_class_equality
    {g h : YmLangTfdClass}
    (same :
      ymLangTfdSameConditionalReadout ymLangTfdFiniteObligations g h) :
    g = h :=
  ymLangTfd_conditional_tannakian_reduction
    ymLangTfdFiniteObligations same

end BEDC.Derived.Visions
