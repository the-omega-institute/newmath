import BEDC.Derived.LegendreDichotomyUp
import BEDC.Derived.FermatLittleUp

namespace BEDC.Derived.QuadraticResidueCountUp

open BEDC.Algebra.FiniteFold
open BEDC.Derived.EulerCriterionUp
open BEDC.Derived.FermatLittleUp
open BEDC.Derived.LegendreDichotomyUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

private theorem bool_not_true_eq_false {b : Bool} :
    (!b) = true -> b = false := by
  cases b with
  | false =>
      intro _h
      rfl
  | true =>
      intro h
      cases h

private theorem bool_not_false_eq_true {b : Bool} :
    b = false -> (!b) = true := by
  intro h
  rw [h]
  rfl

private theorem nat_add_left_cancel_pure (a : Nat) :
    ∀ b c : Nat, a + b = a + c -> b = c
  | b, c, h => by
      induction a with
      | zero =>
          exact (Nat.zero_add b).symm.trans (h.trans (Nat.zero_add c))
      | succ a ih =>
          have hsucc : Nat.succ (a + b) = Nat.succ (a + c) :=
            (Nat.succ_add a b).symm.trans (h.trans (Nat.succ_add a c))
          exact ih (Nat.succ.inj hsucc)

private theorem mem_filter_bool_source {A : Type u} (keep : A -> Bool) :
    ∀ {xs : List A} {x : A}, x ∈ xs.filter keep -> x ∈ xs
  | [], _x, mem => by
      cases mem
  | y :: ys, x, mem => by
      cases hit : keep y with
      | false =>
          have filterEq :
              List.filter keep (y :: ys) = List.filter keep ys :=
            List.filter_cons_of_neg (p := keep) (a := y) (l := ys)
              (by
                intro htrue
                rw [hit] at htrue
                cases htrue)
          rw [filterEq] at mem
          exact List.Mem.tail y (mem_filter_bool_source keep mem)
      | true =>
          have filterEq :
              List.filter keep (y :: ys) = y :: List.filter keep ys :=
            List.filter_cons_of_pos (p := keep) (a := y) (l := ys) hit
          rw [filterEq] at mem
          cases mem with
          | head =>
              exact List.Mem.head ys
          | tail _ tailMem =>
              exact List.Mem.tail y (mem_filter_bool_source keep tailMem)

private theorem mem_filter_bool_keep {A : Type u} (keep : A -> Bool) :
    ∀ {xs : List A} {x : A}, x ∈ xs.filter keep -> keep x = true
  | [], _x, mem => by
      cases mem
  | y :: ys, x, mem => by
      cases hit : keep y with
      | false =>
          have filterEq :
              List.filter keep (y :: ys) = List.filter keep ys :=
            List.filter_cons_of_neg (p := keep) (a := y) (l := ys)
              (by
                intro htrue
                rw [hit] at htrue
                cases htrue)
          rw [filterEq] at mem
          exact mem_filter_bool_keep keep mem
      | true =>
          have filterEq :
              List.filter keep (y :: ys) = y :: List.filter keep ys :=
            List.filter_cons_of_pos (p := keep) (a := y) (l := ys) hit
          rw [filterEq] at mem
          cases mem with
          | head =>
              exact hit
          | tail _ tailMem =>
              exact mem_filter_bool_keep keep tailMem

private theorem mem_filter_bool_intro {A : Type u} (keep : A -> Bool) :
    ∀ {xs : List A} {x : A}, x ∈ xs -> keep x = true -> x ∈ xs.filter keep
  | [], _x, mem, _hit => by
      cases mem
  | y :: ys, x, mem, hit => by
      unfold List.filter
      cases mem with
      | head =>
          rw [hit]
          exact List.Mem.head (List.filter keep ys)
      | tail _ tailMem =>
          cases keep y with
          | false =>
              exact mem_filter_bool_intro keep tailMem hit
          | true =>
              exact List.Mem.tail y (mem_filter_bool_intro keep tailMem hit)

private theorem filter_bool_nodup {A : Type u} (keep : A -> Bool) :
    ∀ {xs : List A}, ListNoDup xs -> ListNoDup (xs.filter keep)
  | [], _nodup =>
      ListNoDup.nil
  | x :: xs, nodup => by
      unfold List.filter
      cases keep x with
      | false =>
          exact filter_bool_nodup keep (listNoDup_tail nodup)
      | true =>
          exact ListNoDup.cons
            (fun memTail =>
              listNoDup_head_not_mem nodup
                (mem_filter_bool_source keep memTail))
            (filter_bool_nodup keep (listNoDup_tail nodup))

private theorem filter_bool_length_partition {A : Type u} (keep : A -> Bool) :
    ∀ xs : List A,
      (xs.filter keep).length +
          (xs.filter (fun x : A => !(keep x))).length =
        xs.length
  | [] =>
      rfl
  | x :: xs => by
      unfold List.filter
      cases keep x with
      | false =>
          change
            (xs.filter keep).length +
                Nat.succ ((xs.filter (fun y : A => !(keep y))).length) =
              Nat.succ xs.length
          rw [Nat.add_succ, filter_bool_length_partition keep xs]
      | true =>
          change
            Nat.succ ((xs.filter keep).length) +
                (xs.filter (fun y : A => !(keep y))).length =
              Nat.succ xs.length
          rw [Nat.succ_add, filter_bool_length_partition keep xs]

private theorem filter_bool_partition_perm {A : Type u} (keep : A -> Bool) :
    ∀ xs : List A,
      ListPerm xs
        (xs.filter keep ++ xs.filter (fun x : A => !(keep x)))
  | [] =>
      ListPerm.nil
  | x :: xs => by
      unfold List.filter
      cases keep x with
      | false =>
          exact ListPerm.trans
            (ListPerm.cons x (filter_bool_partition_perm keep xs))
            (listPerm_symm
              (listPerm_middle x (xs.filter keep)
                (xs.filter (fun y : A => !(keep y)))))
      | true =>
          exact ListPerm.cons x (filter_bool_partition_perm keep xs)

def quadraticResidues {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) : List (ZMod p) :=
  (nonzeroResidues prime).filter (fun x : ZMod p => legendreQRSearch prime x)

def nonquadraticResidues {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) : List (ZMod p) :=
  (nonzeroResidues prime).filter (fun x : ZMod p => !(legendreQRSearch prime x))

theorem quadraticResidues_nodup {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) :
    ListNoDup (quadraticResidues prime) := by
  unfold quadraticResidues
  exact filter_bool_nodup
    (fun x : ZMod p => legendreQRSearch prime x)
    (nonzeroResidues_nodup prime)

theorem nonquadraticResidues_nodup {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) :
    ListNoDup (nonquadraticResidues prime) := by
  unfold nonquadraticResidues
  exact filter_bool_nodup
    (fun x : ZMod p => !(legendreQRSearch prime x))
    (nonzeroResidues_nodup prime)

theorem quadraticResidues_mem_nonzero {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) {x : ZMod p} :
    x ∈ quadraticResidues prime -> x ∈ nonzeroResidues prime := by
  intro mem
  unfold quadraticResidues at mem
  exact mem_filter_bool_source
    (fun y : ZMod p => legendreQRSearch prime y) mem

theorem nonquadraticResidues_mem_nonzero {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) {x : ZMod p} :
    x ∈ nonquadraticResidues prime -> x ∈ nonzeroResidues prime := by
  intro mem
  unfold nonquadraticResidues at mem
  exact mem_filter_bool_source
    (fun y : ZMod p => !(legendreQRSearch prime y)) mem

theorem quadraticResidues_all_nonzero {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) :
    ∀ x : ZMod p, x ∈ quadraticResidues prime -> zmodNonzero x := by
  intro x mem
  exact nonzeroResidues_all_nonzero prime x
    (quadraticResidues_mem_nonzero prime mem)

theorem nonquadraticResidues_all_nonzero {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) :
    ∀ x : ZMod p, x ∈ nonquadraticResidues prime -> zmodNonzero x := by
  intro x mem
  exact nonzeroResidues_all_nonzero prime x
    (nonquadraticResidues_mem_nonzero prime mem)

theorem quadraticResidues_sound {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) {x : ZMod p} :
    x ∈ quadraticResidues prime -> IsQR prime x := by
  intro mem
  unfold quadraticResidues at mem
  have hit : legendreQRSearch prime x = true :=
    mem_filter_bool_keep
      (fun y : ZMod p => legendreQRSearch prime y) mem
  exact legendreQRSearch_sound prime hit

theorem nonquadraticResidues_sound {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) {x : ZMod p} :
    x ∈ nonquadraticResidues prime -> LegendreNonresidue prime x := by
  intro mem
  unfold nonquadraticResidues at mem
  have nonzero : zmodNonzero x :=
    nonzeroResidues_all_nonzero prime x
      (mem_filter_bool_source
        (fun y : ZMod p => !(legendreQRSearch prime y)) mem)
  have missed : legendreQRSearch prime x = false :=
    bool_not_true_eq_false
      (mem_filter_bool_keep
        (fun y : ZMod p => !(legendreQRSearch prime y)) mem)
  exact legendreQRSearch_nonresidue_of_false prime nonzero missed

theorem quadraticResidues_complete {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) {x : ZMod p} :
    zmodNonzero x -> IsQR prime x -> x ∈ quadraticResidues prime := by
  intro nonzero qr
  unfold quadraticResidues
  exact mem_filter_bool_intro
    (fun y : ZMod p => legendreQRSearch prime y)
    (nonzero_residues_complete prime x nonzero)
    (legendreQRSearch_complete prime nonzero qr)

theorem nonquadraticResidues_complete {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) {x : ZMod p} :
    LegendreNonresidue prime x -> x ∈ nonquadraticResidues prime := by
  intro nonresidue
  unfold nonquadraticResidues
  exact mem_filter_bool_intro
    (fun y : ZMod p => !(legendreQRSearch prime y))
    (nonzero_residues_complete prime x nonresidue.left)
    (bool_not_false_eq_true
      (legendreQRSearch_false_of_nonresidue prime nonresidue))

theorem nonzeroResidues_mem_quadratic_or_nonquadratic
    {p : BEDC.FKernel.Hist.BHist} (prime : NatPrime p) {x : ZMod p} :
    x ∈ nonzeroResidues prime ->
      x ∈ quadraticResidues prime ∨ x ∈ nonquadraticResidues prime := by
  intro mem
  cases found : legendreQRSearch prime x with
  | false =>
      exact Or.inr
        (by
          unfold nonquadraticResidues
          exact mem_filter_bool_intro
            (fun y : ZMod p => !(legendreQRSearch prime y))
            mem
            (bool_not_false_eq_true found))
  | true =>
      exact Or.inl
        (by
          unfold quadraticResidues
          exact mem_filter_bool_intro
            (fun y : ZMod p => legendreQRSearch prime y) mem found)

theorem nonzero_quadratic_or_nonquadratic
    {p : BEDC.FKernel.Hist.BHist} (prime : NatPrime p) {x : ZMod p} :
    zmodNonzero x ->
      x ∈ quadraticResidues prime ∨ x ∈ nonquadraticResidues prime := by
  intro nonzero
  exact nonzeroResidues_mem_quadratic_or_nonquadratic prime
    (nonzero_residues_complete prime x nonzero)

theorem nonzeroResidues_quadratic_nonquadratic_perm
    {p : BEDC.FKernel.Hist.BHist} (prime : NatPrime p) :
    ListPerm (nonzeroResidues prime)
      (quadraticResidues prime ++ nonquadraticResidues prime) := by
  unfold quadraticResidues
  unfold nonquadraticResidues
  exact filter_bool_partition_perm
    (fun x : ZMod p => legendreQRSearch prime x)
    (nonzeroResidues prime)

theorem quadratic_nonquadratic_length_partition
    {p : BEDC.FKernel.Hist.BHist} (prime : NatPrime p) :
    (quadraticResidues prime).length +
        (nonquadraticResidues prime).length =
      (nonzeroResidues prime).length := by
  unfold quadraticResidues
  unfold nonquadraticResidues
  exact filter_bool_length_partition
    (fun x : ZMod p => legendreQRSearch prime x)
    (nonzeroResidues prime)

theorem nonquadraticResidues_length_of_quadraticResidues_length
    {p : BEDC.FKernel.Hist.BHist} (prime : NatPrime p) {h : Nat} :
    eulerHalfExponent p h ->
      (quadraticResidues prime).length = h ->
        (nonquadraticResidues prime).length = h := by
  intro half qrCount
  have partition := quadratic_nonquadratic_length_partition prime
  rw [qrCount] at partition
  rw [nonzeroResidues_length prime] at partition
  have sameDouble :
      h + (nonquadraticResidues prime).length = h + h :=
    partition.trans half.symm
  exact nat_add_left_cancel_pure h
    (nonquadraticResidues prime).length h sameDouble

def QuadraticResidueHalfCount {p : BEDC.FKernel.Hist.BHist}
    (prime : NatPrime p) (h : Nat) : Prop :=
  eulerHalfExponent p h ∧
    (quadraticResidues prime).length = h ∧
      (nonquadraticResidues prime).length = h

theorem quadraticResidueHalfCount_of_quadraticResidues_length
    {p : BEDC.FKernel.Hist.BHist} (prime : NatPrime p) {h : Nat} :
    eulerHalfExponent p h ->
      (quadraticResidues prime).length = h ->
        QuadraticResidueHalfCount prime h := by
  intro half qrCount
  exact ⟨half, qrCount,
    nonquadraticResidues_length_of_quadraticResidues_length
      prime half qrCount⟩

end BEDC.Derived.QuadraticResidueCountUp
