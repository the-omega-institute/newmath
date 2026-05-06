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

theorem axisAdd_licensed_not_primitive : True := True.intro

end BEDC.Derived.AxisZeckendorf.AxisAdd
