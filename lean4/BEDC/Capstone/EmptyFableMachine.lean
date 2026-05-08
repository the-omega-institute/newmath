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

/-- `Trace h xs` records that `h` is generated from `BHist.Empty` by the
sequence of marks `xs` read in chronological order. The selector at
constructor `e0` is `b0`; at `e1` it is `b1`. -/
inductive Trace : BHist → List BMark → Prop
  | nil  : Trace BHist.Empty []
  | zero (h : BHist) (xs : List BMark) :
      Trace h xs → Trace (BHist.e0 h) (xs ++ [BMark.b0])
  | one  (h : BHist) (xs : List BMark) :
      Trace h xs → Trace (BHist.e1 h) (xs ++ [BMark.b1])

theorem trace_exists : ∀ h : BHist, ∃ xs : List BMark, Trace h xs := by
  intro h
  induction h with
  | Empty => exact ⟨[], Trace.nil⟩
  | e0 k ih =>
      cases ih with
      | intro xs hxs => exact ⟨xs ++ [BMark.b0], Trace.zero k xs hxs⟩
  | e1 k ih =>
      cases ih with
      | intro xs hxs => exact ⟨xs ++ [BMark.b1], Trace.one k xs hxs⟩

theorem trace_empty_iff {h : BHist} : Trace h [] ↔ h = BHist.Empty := by
  constructor
  · intro tr
    generalize hxs : ([] : List BMark) = ys at tr
    cases tr with
    | nil => rfl
    | zero h0 xs _ =>
        have : xs ++ [BMark.b0] = [] := hxs.symm
        cases xs <;> cases this
    | one h0 xs _ =>
        have : xs ++ [BMark.b1] = [] := hxs.symm
        cases xs <;> cases this
  · intro h_eq
    cases h_eq
    exact Trace.nil

theorem trace_hsame_transport {h k : BHist} {xs : List BMark} :
    hsame h k → Trace h xs → Trace k xs := by
  intro same tr
  cases same
  exact tr

private theorem appendSingletonEq {α : Type u} :
    ∀ {xs ys : List α} {a b : α}, xs ++ [a] = ys ++ [b] → xs = ys ∧ a = b := by
  intro xs
  induction xs with
  | nil =>
      intro ys a b h
      cases ys with
      | nil =>
          injection h with hab _
          constructor
          · rfl
          · exact hab
      | cons y ys =>
          injection h with _ htail
          cases ys <;> cases htail
  | cons x xs ih =>
      intro ys a b h
      cases ys with
      | nil =>
          injection h with _ htail
          cases xs <;> cases htail
      | cons y ys =>
          injection h with hxy htail
          cases hxy
          cases ih htail with
          | intro init last =>
              constructor
              · cases init
                rfl
              · exact last

private theorem trace_snoc_inversion :
    ∀ {h : BHist} {xs : List BMark} {m : BMark},
      Trace h (xs ++ [m]) →
        (m = BMark.b0 ∧ ∃ k, h = BHist.e0 k ∧ Trace k xs) ∨
        (m = BMark.b1 ∧ ∃ k, h = BHist.e1 k ∧ Trace k xs) := by
  intro h xs m tr
  generalize hseq : xs ++ [m] = seq at tr
  cases tr with
  | nil =>
      have impossible : xs ++ [m] = [] := hseq
      cases xs <;> cases impossible
  | zero k ys hk =>
      have heq : ys ++ [BMark.b0] = xs ++ [m] := hseq.symm
      have hpair := appendSingletonEq heq
      cases hpair with
      | intro hinit hlast =>
          cases hlast
          cases hinit
          exact Or.inl ⟨rfl, k, rfl, hk⟩
  | one k ys hk =>
      have heq : ys ++ [BMark.b1] = xs ++ [m] := hseq.symm
      have hpair := appendSingletonEq heq
      cases hpair with
      | intro hinit hlast =>
          cases hlast
          cases hinit
          exact Or.inr ⟨rfl, k, rfl, hk⟩

theorem trace_same_marks_hsame :
    ∀ {xs : List BMark} {h k : BHist}, Trace h xs → Trace k xs → hsame h k := by
  intro xs h k th tk
  induction th generalizing k with
  | nil =>
      have kk : k = BHist.Empty := (trace_empty_iff).mp tk
      cases kk
      rfl
  | zero h0 xs0 th0 ih =>
      cases trace_snoc_inversion tk with
      | inl kcase =>
          cases kcase with
          | intro ky kexists =>
              cases ky
              cases kexists with
              | intro k0 kdata =>
                  cases kdata with
                  | intro kk tk0 =>
                      cases kk
                      have htail := ih tk0
                      cases htail
                      rfl
      | inr kcase =>
          cases kcase with
          | intro ky _ =>
              cases ky
  | one h0 xs0 th0 ih =>
      cases trace_snoc_inversion tk with
      | inl kcase =>
          cases kcase with
          | intro ky _ =>
              cases ky
      | inr kcase =>
          cases kcase with
          | intro ky kexists =>
              cases ky
              cases kexists with
              | intro k0 kdata =>
                  cases kdata with
                  | intro kk tk0 =>
                      cases kk
                      have htail := ih tk0
                      cases htail
                      rfl

/-- `AdNext Γ h m` says: there exists a target `r` such that an empty-step
from `h` enacting `m` is admissible under the local branch predicate `Γ`. -/
def AdNext (Γ : BHist → BMark → BHist → Prop) (h : BHist) (m : BMark) : Prop :=
  ∃ r : BHist, EmptyStep h m r ∧ Γ h m r

/-- `MultiNext Γ h` says both branches `b0` and `b1` are admissible from `h`
under `Γ`. -/
def MultiNext (Γ : BHist → BMark → BHist → Prop) (h : BHist) : Prop :=
  AdNext Γ h BMark.b0 ∧ AdNext Γ h BMark.b1

/-- `SelStep Γ h r` is the selector witness for a realized step from `h` to `r`:
the mark that was enacted, together with the empty-step and `Γ`-admissibility
witnesses. Lives in `Prop`. -/
def SelStep (Γ : BHist → BMark → BHist → Prop) (h r : BHist) : Prop :=
  ∃ m : BMark, EmptyStep h m r ∧ Γ h m r

theorem selStep_exposes_mark
    {Γ : BHist → BMark → BHist → Prop} {h r : BHist} :
    SelStep Γ h r → ∃ m : BMark, EmptyStep h m r := by
  intro hs
  cases hs with
  | intro m data => exact ⟨m, data.left⟩

theorem selStep_from_step
    {Γ : BHist → BMark → BHist → Prop}
    {h r : BHist} {m : BMark} :
    EmptyStep h m r → Γ h m r → SelStep Γ h r := by
  intro hstep hcert
  exact ⟨m, hstep, hcert⟩

theorem selStep_distinct_branches_separated
    {Γ : BHist → BMark → BHist → Prop}
    {h r0 r1 : BHist} :
    SelStep Γ h r0 → SelStep Γ h r1 →
    -- if the two selectors recovered are distinct marks, the targets diverge
    (∀ m0 m1 : BMark, EmptyStep h m0 r0 → EmptyStep h m1 r1 →
      ¬ msame m0 m1 → ¬ hsame r0 r1) := by
  intro _ _ m0 m1 step0 step1 mneq same
  cases step0 <;> cases step1 <;>
    first
    | exact mneq rfl
    | exact not_hsame_e0_e1 same
    | exact not_hsame_e1_e0 same

theorem multiNext_iff
    {Γ : BHist → BMark → BHist → Prop} {h : BHist} :
    MultiNext Γ h ↔ AdNext Γ h BMark.b0 ∧ AdNext Γ h BMark.b1 := Iff.rfl

end BEDC.Capstone.EmptyFableMachine
