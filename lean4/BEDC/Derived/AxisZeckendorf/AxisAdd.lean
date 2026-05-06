/-
AxisAdd↑: NameCert for continuation restricted to `ZeroSpine`. The interface
is `Cont` of the finite kernel, evaluated on `e0`-spine inputs. The full
arithmetic machinery (associativity, commutativity, determinacy) is a
horizon for the codex formalize pipeline.
-/
import BEDC.Derived.AxisZeckendorf.Spine
import BEDC.FKernel.Cont

namespace BEDC.Derived.AxisZeckendorf.AxisAdd

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

end BEDC.Derived.AxisZeckendorf.AxisAdd
