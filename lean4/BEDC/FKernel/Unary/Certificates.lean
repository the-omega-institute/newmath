import BEDC.FKernel.Unary.Domain

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont

def UnaryPatternSpec : Prop :=
  UnaryHistory BHist.Empty /\
    forall {h : BHist}, UnaryHistory h -> UnaryHistory (BHist.e1 h)

theorem UnaryPatternSpec_fields :
    UnaryPatternSpec ↔
      UnaryHistory BHist.Empty ∧
        (forall {h : BHist}, UnaryHistory h -> UnaryHistory (BHist.e1 h)) := by
  rfl

theorem UnaryPatternSpec_step (spec : UnaryPatternSpec) {h : BHist} :
    UnaryHistory h -> UnaryHistory (BHist.e1 h) := by
  intro uh
  exact spec.right uh

theorem UnaryPatternSpec_nonempty : Nonempty UnaryPatternSpec := by
  exact Nonempty.intro (And.intro unary_empty (fun uh => unary_e1_closed uh))

def UnaryClassifierSpec (h k : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ hsame h k

theorem UnaryClassifierSpec_iff_fields {h k : BHist} :
    UnaryClassifierSpec h k <-> UnaryHistory h ∧ UnaryHistory k ∧ hsame h k := by
  rfl

def UnaryLedgerPolicy : Prop :=
  forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r

theorem UnaryLedgerPolicy_iff_unary_cont_closed :
    UnaryLedgerPolicy ↔
      (forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r) := by
  rfl

theorem unaryLedgerPolicy_from_unary_cont_closed : UnaryLedgerPolicy := by
  intro h k r uh uk cont
  exact unary_cont_closed uh uk cont

theorem nat_up_name_certificate :
    NameCert UnaryHistory UnaryClassifierSpec := by
  constructor
  · exact ⟨BHist.Empty, unary_empty⟩
  · intro h uh
    exact ⟨uh, uh, hsame_refl h⟩
  · intro h k same
    exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
  · intro h k r hk kr
    exact ⟨hk.left, kr.right.left, hsame_trans hk.right.right kr.right.right⟩
  · intro h k same _
    exact same.right.left

theorem nat_up_name_certificate_exists :
    Nonempty (NameCert UnaryHistory UnaryClassifierSpec) := by
  exact Nonempty.intro nat_up_name_certificate

theorem nat_up_semantic_name_certificate :
    SemanticNameCert UnaryHistory UnaryHistory UnaryHistory UnaryClassifierSpec := by
  constructor
  · exact nat_up_name_certificate
  · intro h source
    exact source
  · intro h source
    exact source

theorem nat_up_licensed_not_primitive :
    NameCert UnaryHistory UnaryClassifierSpec ∧
      Nonempty (NameCert UnaryHistory UnaryClassifierSpec) := by
  constructor
  · exact nat_up_name_certificate
  · exact nat_up_name_certificate_exists

theorem nat_up_certificate_seed_not_primitive :
    NameCert UnaryHistory UnaryClassifierSpec ∧
      Nonempty (NameCert UnaryHistory UnaryClassifierSpec) := by
  exact nat_up_licensed_not_primitive

theorem nat_up_interface_seed :
    UnaryHistory BHist.Empty ∧ UnaryLedgerPolicy ∧
      Nonempty (NameCert UnaryHistory UnaryClassifierSpec) := by
  constructor
  · exact unary_empty
  · constructor
    · exact unaryLedgerPolicy_from_unary_cont_closed
    · exact nat_up_name_certificate_exists

def AddSourceSpec (h k r : BHist) : Prop :=
  UnaryHistory h ∧ UnaryHistory k ∧ Cont h k r

theorem AddSourceSpec_from_unary_cont {h k r : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> AddSourceSpec h k r := by
  intro uh uk cont
  exact And.intro uh (And.intro uk cont)

theorem AddSourceSpec_result_unary {h k r : BHist} :
    AddSourceSpec h k r -> UnaryHistory r := by
  intro spec
  exact unary_cont_preserves_unary_by_induction spec.left spec.right.left spec.right.right

def AddLedgerPolicy : Prop :=
  forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r

theorem AddLedgerPolicy_iff_unary_cont_closed :
    AddLedgerPolicy ↔
      (forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r) := by
  rfl

theorem addLedgerPolicy_from_unary_cont_closed : AddLedgerPolicy := by
  intro h k r uh uk cont
  exact unary_cont_closed uh uk cont

theorem additive_pattern_result_unary_iff_inputs {h k r : BHist} :
    Cont h k r -> (UnaryHistory h /\ UnaryHistory k <-> UnaryHistory r) := by
  intro hr
  exact unary_cont_factors_iff_result hr

def AddClassifierSpec (r r' : BHist) : Prop :=
  hsame r r'

theorem AddSourceSpec_same_source_classifier {h k r r' : BHist} :
    AddSourceSpec h k r -> AddSourceSpec h k r' ->
      AddClassifierSpec r r' ∧ Cont h k r ∧ Cont h k r' ∧
        UnaryHistory r ∧ UnaryHistory r' := by
  intro left right
  have sameRR' : AddClassifierSpec r r' :=
    cont_deterministic left.right.right right.right.right
  exact And.intro sameRR'
    (And.intro left.right.right
      (And.intro right.right.right
        (And.intro (AddSourceSpec_result_unary left) (AddSourceSpec_result_unary right))))

theorem add_up_name_certificate :
    NameCert UnaryHistory AddClassifierSpec := by
  constructor
  · exact ⟨BHist.Empty, unary_empty⟩
  · intro h _
    exact hsame_refl h
  · intro h k same
    exact hsame_symm same
  · intro h k r hk kr
    exact hsame_trans hk kr
  · intro h k same uh
    exact unary_transport uh same

theorem add_up_name_certificate_exists :
    Nonempty (NameCert UnaryHistory AddClassifierSpec) := by
  exact Nonempty.intro add_up_name_certificate

theorem add_up_licensed_not_primitive :
    NameCert UnaryHistory AddClassifierSpec ∧ Nonempty (NameCert UnaryHistory AddClassifierSpec) := by
  exact And.intro add_up_name_certificate add_up_name_certificate_exists

theorem unary_addition_like_unit_with_certificate :
    Nonempty (NameCert UnaryHistory AddClassifierSpec) ∧
      (forall {h left right : BHist},
        UnaryHistory h -> Cont h BHist.Empty left -> Cont BHist.Empty h right ->
          UnaryHistory left ∧ UnaryHistory right ∧ hsame left h ∧ hsame right h) := by
  constructor
  · exact add_up_name_certificate_exists
  · intro h left right uh hleft hright
    exact unary_cont_unit uh hleft hright

theorem unary_addition_like_unit_spine {h left right : BHist} :
    UnaryHistory h -> Cont h BHist.Empty left -> Cont BHist.Empty h right ->
      UnaryHistory left ∧ UnaryHistory right ∧ hsame left h ∧ hsame right h := by
  intro uh hleft hright
  exact unary_cont_unit uh hleft hright

theorem unary_addition_seed_from_policy :
    AddLedgerPolicy -> forall {h k r : BHist},
      UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r := by
  intro policy h k r uh uk cont
  exact policy uh uk cont

theorem unary_addition_seed :
    NameCert UnaryHistory AddClassifierSpec ∧ AddLedgerPolicy := by
  constructor
  · exact add_up_name_certificate
  · exact addLedgerPolicy_from_unary_cont_closed

end BEDC.FKernel.Unary
