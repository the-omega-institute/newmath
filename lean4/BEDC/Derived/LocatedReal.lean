import BEDC.Algebra.Rel.Basic
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.RationalUp.FieldLaws

namespace BEDC.Derived.LocatedReal

open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

private def p1 (k : Nat) : Nat :=
  Nat.succ k

private def p2 (k : Nat) : Nat :=
  Nat.succ (p1 k)

private def p3 (k : Nat) : Nat :=
  Nat.succ (p2 k)

private def p4 (k : Nat) : Nat :=
  Nat.succ (p3 k)

private def natMax : Nat -> Nat -> Nat
  | 0, b => b
  | Nat.succ a, 0 => Nat.succ a
  | Nat.succ a, Nat.succ b => Nat.succ (natMax a b)

private theorem natMax_left (a b : Nat) : a ≤ natMax a b := by
  induction a generalizing b with
  | zero =>
      exact Nat.zero_le (natMax 0 b)
  | succ a ih =>
      cases b with
      | zero =>
          exact Nat.le_refl (Nat.succ a)
      | succ b =>
          change Nat.succ a ≤ Nat.succ (natMax a b)
          exact Nat.succ_le_succ (ih b)

private theorem natMax_right (a b : Nat) : b ≤ natMax a b := by
  induction a generalizing b with
  | zero =>
      change b ≤ b
      exact Nat.le_refl b
  | succ a ih =>
      cases b with
      | zero =>
          exact Nat.zero_le (natMax (Nat.succ a) 0)
      | succ b =>
          change Nat.succ b ≤ Nat.succ (natMax a b)
          exact Nat.succ_le_succ (ih b)

private theorem natMax_le {a b c : Nat} :
    a ≤ c -> b ≤ c -> natMax a b ≤ c := by
  intro ha hb
  induction a generalizing b c with
  | zero =>
      change b ≤ c
      exact hb
  | succ a ih =>
      cases b with
      | zero =>
          change Nat.succ a ≤ c
          exact ha
      | succ b =>
          cases c with
          | zero =>
              cases ha
          | succ c =>
              change Nat.succ (natMax a b) ≤ Nat.succ c
              exact Nat.succ_le_succ
                (ih (Nat.le_of_succ_le_succ ha)
                  (Nat.le_of_succ_le_succ hb))

private theorem p1_le_p3 (k : Nat) : p1 k ≤ p3 k := by
  apply Nat.succ_le_succ
  exact Nat.le_trans (Nat.le_succ k) (Nat.le_succ (Nat.succ k))

private theorem p2_le_p3 (k : Nat) : p2 k ≤ p3 k := by
  exact Nat.le_succ (p2 k)

private theorem p1_le_p2 (k : Nat) : p1 k ≤ p2 k := by
  exact Nat.le_succ (p1 k)

private theorem p3_le_p4 (k : Nat) : p3 k ≤ p4 k := by
  exact Nat.le_succ (p3 k)

private theorem p2_eq_p1_p1 (k : Nat) : p2 k = p1 (p1 k) := by
  rfl

private theorem p4_eq_p3_p1 (k : Nat) : p4 k = p3 (p1 k) := by
  rfl

private theorem p4_eq_p1_p3 (k : Nat) : p4 k = p1 (p3 k) := by
  rfl

private def natHist (n : Nat) : BHist :=
  BEDC.Derived.IntUp.natToUnary n

private theorem natHist_unary (n : Nat) : UnaryHistory (natHist n) :=
  BEDC.Derived.IntUp.natToUnary_unary n

private theorem natHist_length (n : Nat) :
    BEDC.FKernel.ExternalBinary.bwordLength (natHist n) = n :=
  BEDC.Derived.IntUp.natToUnary_length n

def powTwoNat : Nat -> Nat
  | 0 => 1
  | Nat.succ k => 2 * powTwoNat k

theorem powTwoNat_pos (k : Nat) : 0 < powTwoNat k := by
  induction k with
  | zero =>
      exact Nat.succ_pos 0
  | succ k ih =>
      exact Nat.mul_pos (Nat.succ_pos 1) ih

theorem powTwoNat_succ_gt_one (k : Nat) : 1 < powTwoNat (Nat.succ k) := by
  change 1 < 2 * powTwoNat k
  calc
    1 < 2 := Nat.lt_succ_self 1
    _ ≤ 2 * powTwoNat k := by
      exact Nat.mul_le_mul_left 2 (powTwoNat_pos k)

private theorem dyadicDenPos (k : Nat) :
    NatUnaryStrictPrefix NatOne (natHist (powTwoNat k)) ∨
      hsame (natHist (powTwoNat k)) NatOne := by
  cases k with
  | zero =>
      exact Or.inr
        ((BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
          (natHist_unary (powTwoNat 0)) (unary_e1_closed unary_empty)).mpr
          (by
            change BEDC.FKernel.ExternalBinary.bwordLength (natHist 1) =
              BEDC.FKernel.ExternalBinary.bwordLength NatOne
            rw [natHist_length]
            change 1 = BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 BHist.Empty)
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
              BHist.Empty unary_empty]
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]))
  | succ k =>
      apply Or.inl
      apply NatUnaryStrictPrefix_of_length_lt
      · exact unary_e1_closed unary_empty
      · exact natHist_unary (powTwoNat (Nat.succ k))
      · change
          BEDC.FKernel.ExternalBinary.bwordLength NatOne <
            BEDC.FKernel.ExternalBinary.bwordLength (natHist (powTwoNat (Nat.succ k)))
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
          BHist.Empty unary_empty]
        rw [natHist_length]
        exact powTwoNat_succ_gt_one k

def dyadicRat (k : Nat) : Rat :=
  { num := BEDC.Derived.RationalUp.intOne
    den := natHist (powTwoNat k)
    den_pos := dyadicDenPos k }

structure RatMetricKit where
  close : Rat -> Rat -> Nat -> Prop
  apart : Rat -> Rat -> Nat -> Prop
  le : Rat -> Rat -> Prop
  close_refl : ∀ (x : Rat) (k : Nat), close x x k
  close_symm : ∀ {x y : Rat} {k : Nat}, close x y k -> close y x k
  close_weaken :
    ∀ {x y : Rat} {hi lo : Nat}, lo ≤ hi -> close x y hi -> close x y lo
  close_triangle :
    ∀ {x y z : Rat} {k : Nat},
      close x y (Nat.succ k) -> close y z (Nat.succ k) -> close x z k
  eq_close : ∀ {x y : Rat}, RatEq x y -> ∀ k : Nat, close x y k
  add_close :
    ∀ {x x' y y' : Rat} {k : Nat},
      close x x' (Nat.succ k) -> close y y' (Nat.succ k) ->
        close (ratAdd x y) (ratAdd x' y') k
  neg_close :
    ∀ {x y : Rat} {k : Nat}, close x y k -> close (ratNeg x) (ratNeg y) k
  mul_close :
    ∀ {x x' y y' : Rat} {k : Nat},
      close x x' (Nat.succ k) -> close y y' (Nat.succ k) ->
        close (ratMul x y) (ratMul x' y') k
  le_refl : ∀ x : Rat, le x x
  le_trans : ∀ {x y z : Rat}, le x y -> le y z -> le x z
  le_antisymm : ∀ {x y : Rat}, le x y -> le y x -> RatEq x y
  apart_symm : ∀ {x y : Rat} {k : Nat}, apart x y k -> apart y x k

structure LReal (K : RatMetricKit) where
  seq : Nat -> Rat
  modulus : Nat -> Nat
  modulus_mono : ∀ {i j : Nat}, i ≤ j -> modulus i ≤ modulus j
  cauchy :
    ∀ (k m n : Nat), modulus k ≤ m -> modulus k ≤ n ->
      K.close (seq m) (seq n) k

structure LRealEqData (K : RatMetricKit) (a b : LReal K) where
  modulus : Nat -> Nat
  close :
    ∀ k m n : Nat, modulus k ≤ m -> modulus k ≤ n ->
      K.close (a.seq m) (b.seq n) k

def LRealClose (K : RatMetricKit) (a b : LReal K) (k : Nat) : Prop :=
  ∃ data : LRealEqData K a b,
    ∀ m n : Nat, data.modulus k ≤ m -> data.modulus k ≤ n ->
      K.close (a.seq m) (b.seq n) k

def LRealEq (K : RatMetricKit) (a b : LReal K) : Prop :=
  Nonempty (LRealEqData K a b)

theorem LRealEq_refl (K : RatMetricKit) (a : LReal K) :
    LRealEq K a a := by
  exact ⟨
    { modulus := a.modulus
      close := by
        intro k m n hm hn
        exact a.cauchy k m n hm hn }⟩

theorem LRealEq_symm {K : RatMetricKit} {a b : LReal K} :
    LRealEq K a b -> LRealEq K b a := by
  intro h
  cases h with
  | intro data =>
      exact ⟨
        { modulus := data.modulus
          close := by
            intro k m n hm hn
            exact K.close_symm (data.close k n m hn hm) }⟩

theorem LRealEq_trans {K : RatMetricKit} {a b c : LReal K} :
    LRealEq K a b -> LRealEq K b c -> LRealEq K a c := by
  intro hab hbc
  cases hab with
  | intro ab =>
      cases hbc with
      | intro bc =>
          exact ⟨
            { modulus := fun k => natMax (ab.modulus (p1 k)) (bc.modulus (p1 k))
              close := by
                intro k m n hm hn
                let mid := natMax (ab.modulus (p1 k)) (bc.modulus (p1 k))
                have left :
                    K.close (a.seq m) (b.seq mid) (p1 k) :=
                  ab.close (p1 k) m mid
                    (Nat.le_trans
                      (natMax_left (ab.modulus (p1 k)) (bc.modulus (p1 k))) hm)
                    (natMax_left (ab.modulus (p1 k)) (bc.modulus (p1 k)))
                have right :
                    K.close (b.seq mid) (c.seq n) (p1 k) :=
                  bc.close (p1 k) mid n
                    (natMax_right (ab.modulus (p1 k)) (bc.modulus (p1 k)))
                    (Nat.le_trans
                      (natMax_right (ab.modulus (p1 k)) (bc.modulus (p1 k))) hn)
                exact K.close_triangle left right }⟩

def LRealEquiv (K : RatMetricKit) : RelEquiv (LReal K) where
  rel := LRealEq K
  refl := LRealEq_refl K
  symm := by
    intro x y
    exact LRealEq_symm
  trans := by
    intro x y z
    exact LRealEq_trans

def ratToLReal (K : RatMetricKit) (q : Rat) : LReal K where
  seq := fun _ => q
  modulus := fun _ => 0
  modulus_mono := by
    intro i j hij
    exact Nat.le_refl 0
  cauchy := by
    intro k m n hm hn
    exact K.close_refl q k

theorem ratToLReal_respects {K : RatMetricKit} {q r : Rat} :
    RatEq q r -> LRealEq K (ratToLReal K q) (ratToLReal K r) := by
  intro h
  exact ⟨
    { modulus := fun _ => 0
      close := by
        intro k m n hm hn
        exact K.eq_close h k }⟩

private def joinModulus {K : RatMetricKit} (a b : LReal K) (k : Nat) : Nat :=
  natMax (a.modulus (p3 k)) (b.modulus (p3 k))

private theorem joinModulus_mono {K : RatMetricKit} (a b : LReal K)
    {i j : Nat} :
    i ≤ j -> joinModulus a b i ≤ joinModulus a b j := by
  intro hij
  exact natMax_le
    (Nat.le_trans (a.modulus_mono (Nat.succ_le_succ
      (Nat.succ_le_succ (Nat.succ_le_succ hij))))
      (natMax_left (a.modulus (p3 j)) (b.modulus (p3 j))))
    (Nat.le_trans (b.modulus_mono (Nat.succ_le_succ
      (Nat.succ_le_succ (Nat.succ_le_succ hij))))
      (natMax_right (a.modulus (p3 j)) (b.modulus (p3 j))))

def lrAdd {K : RatMetricKit} (a b : LReal K) : LReal K where
  seq := fun n => ratAdd (a.seq n) (b.seq n)
  modulus := joinModulus a b
  modulus_mono := joinModulus_mono a b
  cauchy := by
    intro k m n hm hn
    have am : a.modulus (p1 k) ≤ m :=
      Nat.le_trans (a.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_left (a.modulus (p3 k)) (b.modulus (p3 k))) hm)
    have an : a.modulus (p1 k) ≤ n :=
      Nat.le_trans (a.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_left (a.modulus (p3 k)) (b.modulus (p3 k))) hn)
    have bm : b.modulus (p1 k) ≤ m :=
      Nat.le_trans (b.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_right (a.modulus (p3 k)) (b.modulus (p3 k))) hm)
    have bn : b.modulus (p1 k) ≤ n :=
      Nat.le_trans (b.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_right (a.modulus (p3 k)) (b.modulus (p3 k))) hn)
    exact K.add_close (a.cauchy (p1 k) m n am an)
      (b.cauchy (p1 k) m n bm bn)

def lrNeg {K : RatMetricKit} (a : LReal K) : LReal K where
  seq := fun n => ratNeg (a.seq n)
  modulus := a.modulus
  modulus_mono := a.modulus_mono
  cauchy := by
    intro k m n hm hn
    exact K.neg_close (a.cauchy k m n hm hn)

def lrMul {K : RatMetricKit} (a b : LReal K) : LReal K where
  seq := fun n => ratMul (a.seq n) (b.seq n)
  modulus := joinModulus a b
  modulus_mono := joinModulus_mono a b
  cauchy := by
    intro k m n hm hn
    have am : a.modulus (p1 k) ≤ m :=
      Nat.le_trans (a.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_left (a.modulus (p3 k)) (b.modulus (p3 k))) hm)
    have an : a.modulus (p1 k) ≤ n :=
      Nat.le_trans (a.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_left (a.modulus (p3 k)) (b.modulus (p3 k))) hn)
    have bm : b.modulus (p1 k) ≤ m :=
      Nat.le_trans (b.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_right (a.modulus (p3 k)) (b.modulus (p3 k))) hm)
    have bn : b.modulus (p1 k) ≤ n :=
      Nat.le_trans (b.modulus_mono (p1_le_p3 k))
        (Nat.le_trans (natMax_right (a.modulus (p3 k)) (b.modulus (p3 k))) hn)
    exact K.mul_close (a.cauchy (p1 k) m n am an)
      (b.cauchy (p1 k) m n bm bn)

theorem lrAdd_respects {K : RatMetricKit} {a a' b b' : LReal K} :
    LRealEq K a a' -> LRealEq K b b' ->
      LRealEq K (lrAdd a b) (lrAdd a' b') := by
  intro ha hb
  cases ha with
  | intro adata =>
      cases hb with
      | intro bdata =>
          exact ⟨
            { modulus := fun k => natMax (adata.modulus (p1 k)) (bdata.modulus (p1 k))
              close := by
                intro k m n hm hn
                have leftClose :
                    K.close (a.seq m) (a'.seq n) (p1 k) :=
                  adata.close (p1 k) m n
                    (Nat.le_trans
                      (natMax_left (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hm)
                    (Nat.le_trans
                      (natMax_left (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hn)
                have rightClose :
                    K.close (b.seq m) (b'.seq n) (p1 k) :=
                  bdata.close (p1 k) m n
                    (Nat.le_trans
                      (natMax_right (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hm)
                    (Nat.le_trans
                      (natMax_right (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hn)
                exact K.add_close leftClose rightClose }⟩

theorem lrNeg_respects {K : RatMetricKit} {a b : LReal K} :
    LRealEq K a b -> LRealEq K (lrNeg a) (lrNeg b) := by
  intro h
  cases h with
  | intro data =>
      exact ⟨
        { modulus := data.modulus
          close := by
            intro k m n hm hn
            exact K.neg_close (data.close k m n hm hn) }⟩

theorem lrMul_respects {K : RatMetricKit} {a a' b b' : LReal K} :
    LRealEq K a a' -> LRealEq K b b' ->
      LRealEq K (lrMul a b) (lrMul a' b') := by
  intro ha hb
  cases ha with
  | intro adata =>
      cases hb with
      | intro bdata =>
          exact ⟨
            { modulus := fun k => natMax (adata.modulus (p1 k)) (bdata.modulus (p1 k))
              close := by
                intro k m n hm hn
                have leftClose :
                    K.close (a.seq m) (a'.seq n) (p1 k) :=
                  adata.close (p1 k) m n
                    (Nat.le_trans
                      (natMax_left (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hm)
                    (Nat.le_trans
                      (natMax_left (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hn)
                have rightClose :
                    K.close (b.seq m) (b'.seq n) (p1 k) :=
                  bdata.close (p1 k) m n
                    (Nat.le_trans
                      (natMax_right (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hm)
                    (Nat.le_trans
                      (natMax_right (adata.modulus (p1 k)) (bdata.modulus (p1 k))) hn)
                exact K.mul_close leftClose rightClose }⟩

def lrLe {K : RatMetricKit} (a b : LReal K) : Prop :=
  ∀ n : Nat, K.le (a.seq n) (b.seq n)

theorem lrLe_refl {K : RatMetricKit} (a : LReal K) : lrLe a a := by
  intro n
  exact K.le_refl (a.seq n)

theorem lrLe_trans {K : RatMetricKit} {a b c : LReal K} :
    lrLe a b -> lrLe b c -> lrLe a c := by
  intro hab hbc n
  exact K.le_trans (hab n) (hbc n)

theorem lrLe_antisymm_eq {K : RatMetricKit} {a b : LReal K} :
    lrLe a b -> lrLe b a -> LRealEq K a b := by
  intro hab hba
  exact ⟨
    { modulus := fun k => natMax (a.modulus (p2 k)) (b.modulus (p2 k))
      close := by
        intro k m n hm hn
        let mid := natMax m n
        have leftHigh :
            K.close (a.seq m) (a.seq mid) (p2 k) := by
          exact a.cauchy (p2 k) m mid
            (Nat.le_trans (natMax_left (a.modulus (p2 k)) (b.modulus (p2 k))) hm)
            (Nat.le_trans
              (Nat.le_trans (natMax_left (a.modulus (p2 k)) (b.modulus (p2 k))) hm)
              (natMax_left m n))
        have middleHigh :
            K.close (a.seq mid) (b.seq mid) (p2 k) :=
          K.eq_close (K.le_antisymm (hab mid) (hba mid)) (p2 k)
        have rightHigh :
            K.close (b.seq mid) (b.seq n) (p2 k) := by
          exact b.cauchy (p2 k) mid n
            (Nat.le_trans
              (Nat.le_trans (natMax_right (a.modulus (p2 k)) (b.modulus (p2 k))) hn)
              (natMax_right m n))
            (Nat.le_trans (natMax_right (a.modulus (p2 k)) (b.modulus (p2 k))) hn)
        have leftMiddle :
            K.close (a.seq m) (b.seq mid) (p1 k) :=
          K.close_triangle leftHigh middleHigh
        have rightMiddle :
            K.close (b.seq mid) (b.seq n) (p1 k) :=
          K.close_weaken (p1_le_p2 k) rightHigh
        exact K.close_triangle leftMiddle rightMiddle }⟩

theorem LRealClose_triangle {K : RatMetricKit} {a b c : LReal K} {k : Nat} :
    LRealClose K a b (p1 k) -> LRealClose K b c (p1 k) ->
      LRealClose K a c k := by
  intro hab hbc
  cases hab with
  | intro ab abAt =>
      cases hbc with
      | intro bc bcAt =>
          exact ⟨
            { modulus := fun j => natMax (ab.modulus (p1 j)) (bc.modulus (p1 j))
              close := by
                intro j m n hm hn
                let mid := natMax (ab.modulus (p1 j)) (bc.modulus (p1 j))
                have left :
                    K.close (a.seq m) (b.seq mid) (p1 j) :=
                  ab.close (p1 j) m mid
                    (Nat.le_trans
                      (natMax_left (ab.modulus (p1 j)) (bc.modulus (p1 j))) hm)
                    (natMax_left (ab.modulus (p1 j)) (bc.modulus (p1 j)))
                have right :
                    K.close (b.seq mid) (c.seq n) (p1 j) :=
                  bc.close (p1 j) mid n
                    (natMax_right (ab.modulus (p1 j)) (bc.modulus (p1 j)))
                    (Nat.le_trans
                      (natMax_right (ab.modulus (p1 j)) (bc.modulus (p1 j))) hn)
                exact K.close_triangle left right },
            by
              intro m n hm hn
              exact K.close_triangle
                (abAt m
                  (natMax (ab.modulus (p1 k)) (bc.modulus (p1 k)))
                  (Nat.le_trans
                    (natMax_left (ab.modulus (p1 k)) (bc.modulus (p1 k))) hm)
                  (natMax_left (ab.modulus (p1 k)) (bc.modulus (p1 k))))
                (bcAt
                  (natMax (ab.modulus (p1 k)) (bc.modulus (p1 k))) n
                  (natMax_right (ab.modulus (p1 k)) (bc.modulus (p1 k)))
                  (Nat.le_trans
                    (natMax_right (ab.modulus (p1 k)) (bc.modulus (p1 k))) hn))⟩

def lrApart {K : RatMetricKit} (a b : LReal K) : Prop :=
  ∃ k : Nat,
    K.apart (a.seq (a.modulus k)) (b.seq (b.modulus k)) k

theorem lrApart_symm {K : RatMetricKit} {a b : LReal K} :
    lrApart a b -> lrApart b a := by
  intro h
  cases h with
  | intro k hk =>
      exact ⟨k, K.apart_symm hk⟩

structure LRealSeqCauchy {K : RatMetricKit} (s : Nat -> LReal K) where
  index : Nat -> Nat
  index_mono : ∀ {i j : Nat}, i ≤ j -> index i ≤ index j
  cauchy :
    ∀ (k m n : Nat), index k ≤ m -> index k ≤ n ->
      K.close
        ((s m).seq ((s m).modulus k))
        ((s n).seq ((s n).modulus k)) k

private def limitModulus {K : RatMetricKit} {s : Nat -> LReal K}
    (C : LRealSeqCauchy s) (k : Nat) : Nat :=
  natMax (p2 k) (C.index (p2 k))

private theorem limitModulus_mono {K : RatMetricKit} {s : Nat -> LReal K}
    (C : LRealSeqCauchy s) {i j : Nat} :
    i ≤ j -> limitModulus C i ≤ limitModulus C j := by
  intro hij
  exact natMax_le
    (Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ hij))
      (natMax_left (p2 j) (C.index (p2 j))))
    (Nat.le_trans (C.index_mono (Nat.succ_le_succ (Nat.succ_le_succ hij)))
      (natMax_right (p2 j) (C.index (p2 j))))

def lrLimit {K : RatMetricKit} (s : Nat -> LReal K)
    (C : LRealSeqCauchy s) : LReal K where
  seq := fun n => (s n).seq ((s n).modulus n)
  modulus := limitModulus C
  modulus_mono := limitModulus_mono C
  cauchy := by
    intro k m n hm hn
    have p2m : p2 k ≤ m :=
      Nat.le_trans (natMax_left (p2 k) (C.index (p2 k))) hm
    have p2n : p2 k ≤ n :=
      Nat.le_trans (natMax_left (p2 k) (C.index (p2 k))) hn
    have im : C.index (p2 k) ≤ m :=
      Nat.le_trans (natMax_right (p2 k) (C.index (p2 k))) hm
    have in' : C.index (p2 k) ≤ n :=
      Nat.le_trans (natMax_right (p2 k) (C.index (p2 k))) hn
    have leftHigh :
        K.close
          ((s m).seq ((s m).modulus m))
          ((s m).seq ((s m).modulus (p2 k))) (p2 k) := by
      exact (s m).cauchy (p2 k) ((s m).modulus m)
        ((s m).modulus (p2 k))
        ((s m).modulus_mono p2m)
        (Nat.le_refl ((s m).modulus (p2 k)))
    have middleHigh :
        K.close
          ((s m).seq ((s m).modulus (p2 k)))
          ((s n).seq ((s n).modulus (p2 k))) (p2 k) :=
      C.cauchy (p2 k) m n im in'
    have rightHigh :
        K.close
          ((s n).seq ((s n).modulus (p2 k)))
          ((s n).seq ((s n).modulus n)) (p2 k) := by
      exact (s n).cauchy (p2 k) ((s n).modulus (p2 k))
        ((s n).modulus n)
        (Nat.le_refl ((s n).modulus (p2 k)))
        ((s n).modulus_mono p2n)
    have leftMiddle :
        K.close
          ((s m).seq ((s m).modulus m))
          ((s n).seq ((s n).modulus (p2 k))) (p1 k) := by
      change
        K.close
          ((s m).seq ((s m).modulus m))
          ((s n).seq ((s n).modulus (p2 k))) (p1 k)
      exact K.close_triangle leftHigh middleHigh
    have rightMiddle :
        K.close
          ((s n).seq ((s n).modulus (p2 k)))
          ((s n).seq ((s n).modulus n)) (p1 k) :=
      K.close_weaken (p1_le_p2 k) rightHigh
    exact K.close_triangle leftMiddle rightMiddle

theorem lrLimit_cauchy {K : RatMetricKit} (s : Nat -> LReal K)
    (C : LRealSeqCauchy s) :
    ∀ (k m n : Nat), (lrLimit s C).modulus k ≤ m ->
      (lrLimit s C).modulus k ≤ n ->
        K.close ((lrLimit s C).seq m) ((lrLimit s C).seq n) k :=
  (lrLimit s C).cauchy

structure LRealApartDivision {K : RatMetricKit}
    (numerator denominator : LReal K)
    (denominator_apart : lrApart denominator (ratToLReal K ratZero)) where
  quotient : LReal K
  quotient_spec : LRealEq K (lrMul quotient denominator) numerator

def lrDivApart {K : RatMetricKit} {numerator denominator : LReal K}
    {denominator_apart : lrApart denominator (ratToLReal K ratZero)}
    (data : LRealApartDivision numerator denominator denominator_apart) :
    LReal K :=
  data.quotient

theorem lrDivApart_spec {K : RatMetricKit} {numerator denominator : LReal K}
    {denominator_apart : lrApart denominator (ratToLReal K ratZero)}
    (data : LRealApartDivision numerator denominator denominator_apart) :
    LRealEq K (lrMul (lrDivApart data) denominator) numerator :=
  data.quotient_spec

end BEDC.Derived.LocatedReal
