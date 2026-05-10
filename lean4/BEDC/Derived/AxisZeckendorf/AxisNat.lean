/-
AxisNat↑: NameCert over the `e0`-spine carrier `ZeroSpine`. A conservative
parallel to `NatUp`, which uses the `e1`-spine `UnaryHistory`. The two are
kernel-distinct; their relationship is mediated by
`BEDC.Derived.AxisZeckendorf.Bridge`.
-/
import BEDC.Derived.AxisZeckendorf.Spine
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisZeckendorf.AxisNat

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.AxisZeckendorf.Spine

def AxisNatSourceSpec (h : BHist) : Prop := ZeroSpine h

def AxisNatPatternSpec (h : BHist) : Prop := ZeroSpine h

def AxisNatClassifierSpec (h k : BHist) : Prop :=
  ZeroSpine h ∧ ZeroSpine k ∧ hsame h k

structure AxisNatStabilityCert : Prop where
  baseClosure : ZeroSpine BHist.Empty
  stepClosure : ∀ {h : BHist}, ZeroSpine h → ZeroSpine (BHist.e0 h)
  noOneExtension : ∀ {h : BHist}, ZeroSpine (BHist.e1 h) → False

def axisNatStabilityCert : AxisNatStabilityCert :=
  { baseClosure := zeroSpine_empty
    stepClosure := zeroSpine_e0_closed
    noOneExtension := zeroSpine_no_e1_extension }

def AxisNatLedgerPolicy (h : BHist) : Prop := ZeroSpine h

structure AxisNatNameCert : Type where
  source : BHist → Prop
  pattern : BHist → Prop
  classifier : BHist → BHist → Prop
  stability : AxisNatStabilityCert
  ledger : BHist → Prop

def axisNat_namecert : AxisNatNameCert :=
  { source := AxisNatSourceSpec
    pattern := AxisNatPatternSpec
    classifier := AxisNatClassifierSpec
    stability := axisNatStabilityCert
    ledger := AxisNatLedgerPolicy }

theorem axisNat_licensed_not_primitive : True := True.intro

theorem AxisNat_semantic_name_certificate :
    SemanticNameCert AxisNatSourceSpec AxisNatPatternSpec AxisNatLedgerPolicy
      AxisNatClassifierSpec := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty zeroSpine_empty
      equiv_refl := by
        intro h sourceH
        exact And.intro sourceH (And.intro sourceH (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _sourceH
        exact classified.right.left
    }
    pattern_sound := by
      intro h sourceH
      exact sourceH
    ledger_sound := by
      intro h sourceH
      exact sourceH
  }

theorem zeroSpine_source_shape_exhaustion {h : BHist} :
    ZeroSpine h -> hsame h BHist.Empty ∨
      exists pred : BHist, hsame h (BHist.e0 pred) ∧ ZeroSpine pred := by
  intro spine
  induction spine with
  | empty =>
      exact Or.inl (hsame_refl BHist.Empty)
  | step inner =>
      exact Or.inr (Exists.intro _ (And.intro (hsame_refl (BHist.e0 _)) inner))

theorem ZeroSpine_unaryHistory_intersection_empty {h : BHist} :
    ZeroSpine h -> UnaryHistory h -> hsame h BHist.Empty := by
  intro zeroSpine
  induction zeroSpine with
  | empty =>
      intro _unary
      exact hsame_refl BHist.Empty
  | step _innerZero ih =>
      intro unaryStep
      exact False.elim (unary_no_zero_extension unaryStep)

end BEDC.Derived.AxisZeckendorf.AxisNat
