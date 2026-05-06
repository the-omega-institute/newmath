/-
AxisAdd↑: NameCert for continuation restricted to `ZeroSpine`. The interface
is `Cont` of the finite kernel, evaluated on `e0`-spine inputs. The full
arithmetic machinery (associativity, commutativity, determinacy) is a
horizon for the codex formalize pipeline.
-/
import BEDC.Derived.AxisZeckendorf.Spine
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AxisZeckendorf.AxisAdd

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.AxisZeckendorf.Spine

def AxisAddSourceSpec (h k : BHist) : Prop :=
  ZeroSpine h ∧ ZeroSpine k

def AxisAddPatternSpec (h k r : BHist) : Prop :=
  ZeroSpine h ∧ ZeroSpine k ∧ Cont h k r

def AxisAddClassifierSpec (h k r₁ r₂ : BHist) : Prop :=
  AxisAddPatternSpec h k r₁ ∧ AxisAddPatternSpec h k r₂ ∧ hsame r₁ r₂

structure AxisAddStabilityCert : Prop where
  leftUnit : ∀ h : BHist, ZeroSpine h → Cont BHist.Empty h h
  closurePending : True

def AxisAddLedgerPolicy (h k r : BHist) : Prop :=
  ZeroSpine h ∧ ZeroSpine k ∧ Cont h k r

structure AxisAddNameCert : Type where
  source : BHist → BHist → Prop
  pattern : BHist → BHist → BHist → Prop
  classifier : BHist → BHist → BHist → BHist → Prop
  stability : AxisAddStabilityCert
  ledger : BHist → BHist → BHist → Prop

def axisAddStabilityCert : AxisAddStabilityCert :=
  { leftUnit := fun h _spine => cont_left_unit h
    closurePending := True.intro }

def axisAdd_namecert : AxisAddNameCert :=
  { source := AxisAddSourceSpec
    pattern := AxisAddPatternSpec
    classifier := AxisAddClassifierSpec
    stability := axisAddStabilityCert
    ledger := AxisAddLedgerPolicy }

theorem AxisAddCont_result_zeroSpine {h k r : BHist} :
    ZeroSpine h -> ZeroSpine k -> Cont h k r -> ZeroSpine r := by
  intro leftSpine rightSpine
  induction rightSpine generalizing r with
  | empty =>
      intro rel
      have same : hsame r h := cont_deterministic rel (cont_right_unit h)
      exact zeroSpine_hsame_transport leftSpine (hsame_symm same)
  | step innerSpine ih =>
      intro rel
      cases (cont_step_result_inversions.left rel) with
      | intro r0 witness =>
          exact witness.left ▸ ZeroSpine.step (ih witness.right)

theorem AxisAddCont_result_determinacy {h k r rPrime : BHist} :
    ZeroSpine h -> ZeroSpine k -> Cont h k r -> Cont h k rPrime ->
      AxisAddClassifierSpec h k r rPrime := by
  intro spineH spineK contR contRPrime
  have patternR : AxisAddPatternSpec h k r :=
    And.intro spineH (And.intro spineK contR)
  have patternRPrime : AxisAddPatternSpec h k rPrime :=
    And.intro spineH (And.intro spineK contRPrime)
  exact And.intro patternR (And.intro patternRPrime (cont_deterministic contR contRPrime))

theorem AxisAddCont_right_unit_zeroSpine {h : BHist} :
    ZeroSpine h -> AxisAddPatternSpec h BHist.Empty h ∧
      AxisAddClassifierSpec h BHist.Empty h h := by
  intro spineH
  have emptySpine : ZeroSpine BHist.Empty := ZeroSpine.empty
  have rightUnit : Cont h BHist.Empty h := cont_right_unit h
  have pattern : AxisAddPatternSpec h BHist.Empty h :=
    And.intro spineH (And.intro emptySpine rightUnit)
  exact And.intro pattern
    (And.intro pattern (And.intro pattern (hsame_refl h)))

theorem AxisAddCont_left_unit_zeroSpine {h : BHist} :
    ZeroSpine h -> AxisAddPatternSpec BHist.Empty h h ∧
      AxisAddClassifierSpec BHist.Empty h h h := by
  intro spineH
  have emptySpine : ZeroSpine BHist.Empty := ZeroSpine.empty
  have leftUnit : Cont BHist.Empty h h := cont_left_unit h
  have pattern : AxisAddPatternSpec BHist.Empty h h :=
    And.intro emptySpine (And.intro spineH leftUnit)
  exact And.intro pattern
    (And.intro pattern (And.intro pattern (hsame_refl h)))

theorem AxisAddCont_associative_zeroSpine {a b c ab bc left right : BHist} :
    ZeroSpine a -> ZeroSpine b -> ZeroSpine c ->
      Cont a b ab -> Cont b c bc -> Cont ab c left -> Cont a bc right ->
        AxisAddPatternSpec ab c left ∧ AxisAddPatternSpec a bc right ∧ hsame left right := by
  intro spineA spineB spineC contAB contBC contLeft contRight
  have spineAB : ZeroSpine ab :=
    AxisAddCont_result_zeroSpine spineA spineB contAB
  have spineBC : ZeroSpine bc :=
    AxisAddCont_result_zeroSpine spineB spineC contBC
  have assocSame : hsame left right :=
    cont_assoc_hsame contAB contLeft contBC contRight
  exact
    And.intro (And.intro spineAB (And.intro spineC contLeft))
      (And.intro (And.intro spineA (And.intro spineBC contRight)) assocSame)

theorem axisAdd_licensed_not_primitive : True := True.intro

theorem AxisAdd_cont_result_zeroSpine {h k r : BHist} :
    ZeroSpine h -> ZeroSpine k -> Cont h k r -> ZeroSpine r := by
  intro spineH spineK contHK
  induction spineK generalizing r with
  | empty =>
      cases contHK
      exact spineH
  | step spineTail tailClosed =>
      cases contHK
      exact ZeroSpine.step (tailClosed rfl)

theorem AxisAddCont_commutative_zeroSpine_shift (h : BHist) {k : BHist} :
    ZeroSpine k -> hsame (append (BHist.e0 h) k) (BHist.e0 (append h k)) := by
  intro spineK
  induction spineK with
  | empty =>
      rfl
  | step _spineTail ih =>
      exact congrArg BHist.e0 ih

theorem AxisAddCont_commutative_zeroSpine_append {h k : BHist} :
    ZeroSpine h -> ZeroSpine k -> hsame (append h k) (append k h) := by
  intro spineH spineK
  induction spineK generalizing h with
  | empty =>
      exact (append_empty_right h).trans (append_empty_left h).symm
  | step spineTail ih =>
      rename_i kTail
      cases h with
      | Empty =>
          exact (append_empty_left (BHist.e0 _)).trans (append_empty_right (BHist.e0 _)).symm
      | e0 hTail =>
          have spineHTail : ZeroSpine hTail := zeroSpine_e0_inversion spineH
          have leftShift := AxisAddCont_commutative_zeroSpine_shift hTail spineTail
          have rightShift :
              hsame (append (BHist.e0 kTail) hTail) (BHist.e0 (append kTail hTail)) :=
            AxisAddCont_commutative_zeroSpine_shift kTail spineHTail
          exact congrArg BHist.e0
            (hsame_trans leftShift
              (hsame_trans (congrArg BHist.e0 (ih spineHTail)) (hsame_symm rightShift)))
      | e1 hTail =>
          exact False.elim (zeroSpine_no_e1_extension spineH)

theorem AxisAddCont_commutative_zeroSpine {h k rHK rKH : BHist} :
    ZeroSpine h -> ZeroSpine k -> Cont h k rHK -> Cont k h rKH -> hsame rHK rKH := by
  intro spineH spineK contHK contKH
  cases contHK
  cases contKH
  exact AxisAddCont_commutative_zeroSpine_append spineH spineK

theorem AxisAdd_semantic_name_certificate {h k : BHist} :
    AxisAddSourceSpec h k ->
      SemanticNameCert (AxisAddPatternSpec h k) (AxisAddPatternSpec h k)
        (AxisAddLedgerPolicy h k) (AxisAddClassifierSpec h k) ∧
        exists r : BHist, AxisAddPatternSpec h k r ∧ ZeroSpine r := by
  intro source
  have sourceH : ZeroSpine h := source.left
  have sourceK : ZeroSpine k := source.right
  have canonicalPattern : AxisAddPatternSpec h k (append h k) :=
    And.intro sourceH (And.intro sourceK (cont_intro rfl))
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro (append h k) canonicalPattern
        equiv_refl := by
          intro r patternR
          exact And.intro patternR (And.intro patternR (hsame_refl r))
        equiv_symm := by
          intro r s classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro r s t classifiedRS classifiedST
          exact And.intro classifiedRS.left
            (And.intro classifiedST.right.left
              (hsame_trans classifiedRS.right.right classifiedST.right.right))
        carrier_respects_equiv := by
          intro r s classified _patternR
          exact classified.right.left
      }
      pattern_sound := by
        intro r patternR
        exact patternR
      ledger_sound := by
        intro r patternR
        exact patternR
    }
  · exact Exists.intro (append h k)
      (And.intro canonicalPattern
        (AxisAddCont_result_zeroSpine sourceH sourceK (cont_intro rfl)))

end BEDC.Derived.AxisZeckendorf.AxisAdd
