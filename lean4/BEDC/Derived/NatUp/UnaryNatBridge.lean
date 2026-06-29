import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History
import BEDC.Derived.NatUp.NatAdd

/-
这是 BEDC unary numeral (UnaryHistory) 到 Lean stdlib Nat 的桥。
加法与序结构保持，mathlib-free，0-axiom。
-/

namespace BEDC.Derived.NatUp.UnaryNatBridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

def unaryLength : BHist → Nat
  | .Empty => 0
  | .e0 h => unaryLength h
  | .e1 h => unaryLength h + 1

def natToUnary : Nat → BHist
  | 0 => .Empty
  | n + 1 => .e1 (natToUnary n)

theorem unaryHistory_natToUnary (n : Nat) : UnaryHistory (natToUnary n) := by
  induction n with
  | zero => exact True.intro
  | succ k ih => exact ih

theorem unaryLength_natToUnary (n : Nat) : unaryLength (natToUnary n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg (· + 1) ih

theorem natToUnary_unaryLength : ∀ {m : BHist}, UnaryHistory m → natToUnary (unaryLength m) = m
  | .Empty, _ => rfl
  | .e1 t, h => congrArg BHist.e1 (natToUnary_unaryLength (m := t) h)
  | .e0 _, h => h.elim

theorem unaryLength_append (m n : BHist) :
    unaryLength (append m n) = unaryLength m + unaryLength n := by
  induction n with
  | Empty => rfl
  | e0 k ih => exact ih
  | e1 k ih =>
      show unaryLength (append m k) + 1 = unaryLength m + (unaryLength k + 1)
      rw [ih, Nat.add_assoc]

theorem unaryLength_natAdd {m n s : BHist} (h : NatAdd m n s) :
    unaryLength s = unaryLength m + unaryLength n := by
  obtain ⟨_, _, hcont⟩ := h
  have hs : s = append m n := hcont
  rw [hs]
  exact unaryLength_append m n

theorem unaryHistory_append {m n : BHist} (hm : UnaryHistory m) (hn : UnaryHistory n) :
    UnaryHistory (append m n) := by
  induction n with
  | Empty =>
      exact hm
  | e0 k ih =>
      cases hn
  | e1 k ih =>
      exact ih hn

theorem unary_eq_of_length_eq {m n : BHist} (hm : UnaryHistory m) (hn : UnaryHistory n)
    (hlen : unaryLength m = unaryLength n) : m = n := by
  exact (natToUnary_unaryLength hm).symm.trans
    ((congrArg natToUnary hlen).trans (natToUnary_unaryLength hn))

theorem nat_add_sub_cancel_left_pure (a c : Nat) : a + c - a = c := by
  induction a with
  | zero =>
      exact (congrArg (fun x => x - 0) (Nat.zero_add c)).trans (Nat.sub_zero c)
  | succ a ih =>
      exact (congrArg (fun x => x - a.succ) (Nat.succ_add a c)).trans
        ((Nat.succ_sub_succ_eq_sub (a + c) a).trans ih)

theorem nat_le_exists_add_pure {a b : Nat} (h : a ≤ b) : ∃ c, b = a + c := by
  induction h with
  | refl =>
      exact ⟨0, (Nat.add_zero a).symm⟩
  | step h ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨c.succ, (congrArg Nat.succ hc).trans (Nat.add_succ a c).symm⟩

theorem nat_add_sub_cancel_of_le_pure {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  obtain ⟨c, hb⟩ := nat_le_exists_add_pure h
  have hsub : b - a = c :=
    (congrArg (fun x => x - a) hb).trans (nat_add_sub_cancel_left_pure a c)
  exact (congrArg (fun x => a + x) hsub).trans hb.symm

def unaryLe (m n : BHist) : Prop :=
  ∃ d, UnaryHistory d ∧ NatAdd m d n

theorem unaryLe_iff {m n : BHist} (hm : UnaryHistory m) (hn : UnaryHistory n) :
    unaryLe m n ↔ unaryLength m ≤ unaryLength n := by
  constructor
  · intro hle
    obtain ⟨d, _, hadd⟩ := hle
    have hlen : unaryLength n = unaryLength m + unaryLength d := unaryLength_natAdd hadd
    exact hlen.symm ▸ Nat.le_add_right (unaryLength m) (unaryLength d)
  · intro hle
    let d := natToUnary (unaryLength n - unaryLength m)
    have hd : UnaryHistory d := unaryHistory_natToUnary (unaryLength n - unaryLength m)
    refine ⟨d, hd, ?_⟩
    refine ⟨hm, hd, ?_⟩
    apply unary_eq_of_length_eq hn (unaryHistory_append hm hd)
    have happend : unaryLength (append m d) = unaryLength m + unaryLength d :=
      unaryLength_append m d
    have hdlen : unaryLength d = unaryLength n - unaryLength m :=
      unaryLength_natToUnary (unaryLength n - unaryLength m)
    have hsum : unaryLength m + (unaryLength n - unaryLength m) = unaryLength n :=
      nat_add_sub_cancel_of_le_pure hle
    exact (happend.trans ((congrArg (fun x => unaryLength m + x) hdlen).trans hsum)).symm

end BEDC.Derived.NatUp.UnaryNatBridge
