import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext

/-! Empty as the fable machine: observer-sequence growth and selector ledgers.

Every BHist is the finite selector ledger of the b0/b1 marks enacted above
`BHist.Empty`. This module formalizes that reading without introducing new
kernel objects: it derives `singletonTail`, `EmptyStep`, `Trace`, `SelStep`,
and `FableLedger` over the existing `BMark`, `BHist`, and `Ext` surface.
-/
namespace BEDC.Capstone.EmptyFableMachine

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext

/-- `singletonTail m` is the one-step Hist that records `m` above `BHist.Empty`.
This is the kernel image of the empty boundary: every fresh distinction is the
application of `e0` or `e1` to `BHist.Empty`. -/
def singletonTail : BMark → BHist
  | BMark.b0 => BHist.e0 BHist.Empty
  | BMark.b1 => BHist.e1 BHist.Empty

/-- An `EmptyStep` from `h` to `r` with mark `m` is exactly an `Ext`-step:
the empty boundary above `h` is filled by enacting `m`. The two are
definitionally equal; the wrapper exists to give the chapter-level reading
a name distinct from the kernel-level relation. -/
def EmptyStep (h : BHist) (m : BMark) (r : BHist) : Prop :=
  Ext h m r

theorem emptyStep_iff_ext {h r : BHist} {m : BMark} :
    EmptyStep h m r ↔ Ext h m r := Iff.rfl

theorem emptyStep_b0_result {h r : BHist} :
    EmptyStep h BMark.b0 r → r = BHist.e0 h := by
  intro hr
  cases hr
  rfl

theorem emptyStep_b1_result {h r : BHist} :
    EmptyStep h BMark.b1 r → r = BHist.e1 h := by
  intro hr
  cases hr
  rfl

theorem emptyStep_result_ne_empty {h r : BHist} {m : BMark} :
    EmptyStep h m r → ¬ hsame r BHist.Empty := by
  intro hr
  exact fun same => ext_result_ne_empty hr same

theorem emptyStep_cross_mark_no_confusion {h r0 r1 : BHist} :
    EmptyStep h BMark.b0 r0 → EmptyStep h BMark.b1 r1 → ¬ hsame r0 r1 := by
  intro left right
  exact fun same => ext_same_source_cross_mark_results_not_hsame left right same

theorem emptyStep_singletonTail_b0 :
    EmptyStep BHist.Empty BMark.b0 (singletonTail BMark.b0) := by
  exact Ext.e0 BHist.Empty

theorem emptyStep_singletonTail_b1 :
    EmptyStep BHist.Empty BMark.b1 (singletonTail BMark.b1) := by
  exact Ext.e1 BHist.Empty

theorem emptyStep_total :
    ∀ (h : BHist) (m : BMark), ∃ r : BHist, EmptyStep h m r := by
  intro h m
  exact ext_total h m

theorem emptyStep_deterministic {h r r' : BHist} {m : BMark} :
    EmptyStep h m r → EmptyStep h m r' → hsame r r' := by
  intro left right
  exact ext_deterministic left right

end BEDC.Capstone.EmptyFableMachine
