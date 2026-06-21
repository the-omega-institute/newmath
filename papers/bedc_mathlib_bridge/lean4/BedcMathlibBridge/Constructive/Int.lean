import BEDC.Derived.IntUp
import BEDC.Derived.NatUp
import BEDC.Derived.PrimeUp
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Unary
import Mathlib.Algebra.Ring.Equiv
import BedcMathlibBridge.Core.RelQuotEquiv

namespace BedcMathlibBridge.Constructive.Int

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)

abbrev append : BHist -> BHist -> BHist :=
  BEDC.FKernel.ExternalBinary.append

def toInt (x : BHist × BHist) : _root_.Int :=
  (bwordLength x.1 : _root_.Int) - (bwordLength x.2 : _root_.Int)

private def diffNorm : Nat -> Nat -> _root_.Int
  | a, 0 => _root_.Int.ofNat a
  | 0, b + 1 => _root_.Int.negSucc b
  | a + 1, b + 1 => diffNorm a b

private theorem diffNorm_ofNat_spec {a b k : Nat}
    (h : diffNorm a b = _root_.Int.ofNat k) : a = b + k := by
  induction a generalizing b k with
  | zero =>
      cases b with
      | zero =>
          change _root_.Int.ofNat 0 = _root_.Int.ofNat k at h
          have hk : 0 = k := _root_.Int.ofNat.inj h
          rw [← hk]
      | succ b =>
          change _root_.Int.negSucc b = _root_.Int.ofNat k at h
          cases h
  | succ a ih =>
      cases b with
      | zero =>
          change _root_.Int.ofNat (Nat.succ a) = _root_.Int.ofNat k at h
          have hk : Nat.succ a = k := _root_.Int.ofNat.inj h
          rw [← hk]
          rw [Nat.zero_add]
      | succ b =>
          change diffNorm a b = _root_.Int.ofNat k at h
          have recEq : a = b + k := ih h
          rw [Nat.succ_add]
          exact congrArg Nat.succ recEq

private theorem diffNorm_negSucc_spec {a b k : Nat}
    (h : diffNorm a b = _root_.Int.negSucc k) : b = a + k + 1 := by
  induction a generalizing b k with
  | zero =>
      cases b with
      | zero =>
          change _root_.Int.ofNat 0 = _root_.Int.negSucc k at h
          cases h
      | succ b =>
          change _root_.Int.negSucc b = _root_.Int.negSucc k at h
          have hk : b = k := _root_.Int.negSucc.inj h
          rw [← hk]
          rw [Nat.zero_add]
  | succ a ih =>
      cases b with
      | zero =>
          change _root_.Int.ofNat (Nat.succ a) = _root_.Int.negSucc k at h
          cases h
      | succ b =>
          change diffNorm a b = _root_.Int.negSucc k at h
          have recEq : b = a + k + 1 := ih h
          rw [Nat.succ_add]
          exact congrArg Nat.succ recEq

private theorem addShuffleOne (b d k : Nat) : b + k + d = d + k + b := by
  calc
    b + k + d = b + (k + d) := Nat.add_assoc b k d
    _ = b + (d + k) := congrArg (fun t => b + t) (Nat.add_comm k d)
    _ = (b + d) + k := (Nat.add_assoc b d k).symm
    _ = (d + b) + k := congrArg (fun t => t + k) (Nat.add_comm b d)
    _ = d + (b + k) := Nat.add_assoc d b k
    _ = d + (k + b) := congrArg (fun t => d + t) (Nat.add_comm b k)
    _ = d + k + b := (Nat.add_assoc d k b).symm

private theorem addShuffleTwo (a c k : Nat) : a + (c + k) = c + (a + k) := by
  rw [Nat.add_left_comm a c k]

private theorem diffNorm_eq_cross {a b c d : Nat}
    (h : diffNorm a b = diffNorm c d) : a + d = c + b := by
  cases hv : diffNorm c d with
  | ofNat k =>
      have left : a = b + k := diffNorm_ofNat_spec (h.trans hv)
      have right : c = d + k := diffNorm_ofNat_spec hv
      rw [left, right]
      exact addShuffleOne b d k
  | negSucc k =>
      have left : b = a + k + 1 := diffNorm_negSucc_spec (h.trans hv)
      have right : d = c + k + 1 := diffNorm_negSucc_spec hv
      rw [left, right]
      change a + (c + (k + 1)) = c + (a + (k + 1))
      exact addShuffleTwo a c (k + 1)

private theorem diffNorm_neg (a b : Nat) : diffNorm b a = -diffNorm a b := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          rfl
      | succ _ =>
          rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          change diffNorm b a = -diffNorm a b
          exact ih b

private theorem subNatNat_zero_right (a : Nat) :
    _root_.Int.subNatNat a 0 = (a : _root_.Int) := by
  cases a with
  | zero =>
      rfl
  | succ _ =>
      unfold _root_.Int.subNatNat
      rw [Nat.zero_sub]
      rfl

private theorem intSubZeroNat (a : Nat) : ((a : _root_.Int) - (0 : _root_.Int)) = a := by
  cases a <;> rfl

private theorem diff_eq_subNatNat (a b : Nat) :
    ((a : _root_.Int) - (b : _root_.Int)) = _root_.Int.subNatNat a b := by
  cases b with
  | zero =>
      rw [subNatNat_zero_right a]
      exact intSubZeroNat a
  | succ _ =>
      cases a <;> rfl

private theorem subNatNat_succ_succ (a b : Nat) :
    _root_.Int.subNatNat (Nat.succ a) (Nat.succ b) = _root_.Int.subNatNat a b := by
  unfold _root_.Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub b a, Nat.succ_sub_succ_eq_sub a b]

private theorem subNatNat_eq_diffNorm (a b : Nat) :
    _root_.Int.subNatNat a b = diffNorm a b := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          rfl
      | succ _ =>
          rfl
  | succ a ih =>
      cases b with
      | zero =>
          rw [subNatNat_zero_right (Nat.succ a)]
          rfl
      | succ b =>
          rw [subNatNat_succ_succ a b]
          exact ih b

private theorem subNatNat_add_add_local (a b k : Nat) :
    _root_.Int.subNatNat (a + k) (b + k) = _root_.Int.subNatNat a b := by
  induction k with
  | zero =>
      rw [Nat.add_zero, Nat.add_zero]
  | succ k ih =>
      rw [Nat.add_succ, Nat.add_succ]
      rw [subNatNat_succ_succ]
      exact ih

private theorem diffNorm_add_add_common (a b k : Nat) :
    diffNorm (a + k) (b + k) = diffNorm a b := by
  rw [← subNatNat_eq_diffNorm (a + k) (b + k)]
  rw [← subNatNat_eq_diffNorm a b]
  exact subNatNat_add_add_local a b k

private theorem diffNorm_zero_right (a : Nat) : diffNorm a 0 = _root_.Int.ofNat a := by
  cases a <;> rfl

private theorem diffNorm_add_right_ofNat (a b c : Nat) :
    diffNorm a b + _root_.Int.ofNat c = diffNorm (a + c) b := by
  induction b generalizing a c with
  | zero =>
      rw [diffNorm_zero_right a, diffNorm_zero_right (a + c)]
      rfl
  | succ b ih =>
      cases a with
      | zero =>
          cases c with
          | zero =>
              rfl
          | succ c =>
              rw [Nat.zero_add]
              change _root_.Int.subNatNat (Nat.succ c) (Nat.succ b) =
                diffNorm (Nat.succ c) (Nat.succ b)
              exact subNatNat_eq_diffNorm (Nat.succ c) (Nat.succ b)
      | succ a =>
          rw [Nat.succ_add]
          change diffNorm a b + _root_.Int.ofNat c = diffNorm (a + c) b
          exact ih a c

private theorem diffNorm_add_right_negSucc (a b d : Nat) :
    diffNorm a b + _root_.Int.negSucc d = diffNorm a (b + Nat.succ d) := by
  induction a generalizing b d with
  | zero =>
      cases b with
      | zero =>
          rw [Nat.zero_add]
          change _root_.Int.ofNat 0 + _root_.Int.negSucc d = _root_.Int.negSucc d
          rfl
      | succ b =>
          rw [Nat.succ_add]
          change _root_.Int.negSucc b + _root_.Int.negSucc d =
            _root_.Int.negSucc (b + Nat.succ d)
          rfl
  | succ a ih =>
      cases b with
      | zero =>
          rw [Nat.zero_add]
          change _root_.Int.subNatNat (Nat.succ a) (Nat.succ d) =
            diffNorm (Nat.succ a) (Nat.succ d)
          exact subNatNat_eq_diffNorm (Nat.succ a) (Nat.succ d)
      | succ b =>
          rw [Nat.succ_add]
          change diffNorm a b + _root_.Int.negSucc d = diffNorm a (b + Nat.succ d)
          exact ih b d

private theorem posNumeratorShuffle (a d k : Nat) : a + (d + k) = a + k + d := by
  calc
    a + (d + k) = a + (k + d) :=
      congrArg (fun t => a + t) (Nat.add_comm d k)
    _ = a + k + d := (Nat.add_assoc a k d).symm

private theorem negDenominatorShuffle (b c k : Nat) :
    b + (c + k + 1) = b + Nat.succ k + c := by
  calc
    b + (c + k + 1) = b + (c + (k + 1)) := by
      rw [Nat.add_assoc c k 1]
    _ = b + ((k + 1) + c) :=
      congrArg (fun t => b + t) (Nat.add_comm c (k + 1))
    _ = b + (k + 1) + c := (Nat.add_assoc b (k + 1) c).symm

private theorem diffNorm_add (a b c d : Nat) :
    diffNorm a b + diffNorm c d = diffNorm (a + c) (b + d) := by
  cases hv : diffNorm c d with
  | ofNat k =>
      have cEq : c = d + k := diffNorm_ofNat_spec hv
      rw [cEq]
      rw [diffNorm_add_right_ofNat a b k]
      rw [posNumeratorShuffle a d k]
      exact (diffNorm_add_add_common (a + k) b d).symm
  | negSucc k =>
      have dEq : d = c + k + 1 := diffNorm_negSucc_spec hv
      rw [dEq]
      rw [diffNorm_add_right_negSucc a b k]
      rw [negDenominatorShuffle b c k]
      exact (diffNorm_add_add_common a (b + Nat.succ k) c).symm

private theorem nat_add_mul_pure (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a + b) * Nat.succ c = (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) := congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) := Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + (a + (b * c + b)) := by
          rw [Nat.add_left_comm (b * c) a b]
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) := by
          rw [Nat.mul_succ]
        _ = a * Nat.succ c + b * Nat.succ c := by
          exact congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem nat_mul_assoc_pure (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem nat_add_perm_four (a b c d : Nat) :
    ((a + b) + (c + d)) + a = ((a + b) + (a + c)) + d := by
  calc
    ((a + b) + (c + d)) + a
        = (a + b) + ((c + d) + a) := Nat.add_assoc (a + b) (c + d) a
    _ = (a + b) + (a + (c + d)) := by rw [Nat.add_comm (c + d) a]
    _ = (a + b) + ((a + c) + d) := by rw [Nat.add_assoc a c d]
    _ = ((a + b) + (a + c)) + d := (Nat.add_assoc (a + b) (a + c) d).symm

private theorem nat_mul_cross_nonneg (b k d l : Nat) :
    (b + k) * (d + l) + b * d = ((b + k) * d + b * (d + l)) + k * l := by
  calc
    (b + k) * (d + l) + b * d
        = ((b + k) * d + (b + k) * l) + b * d := by rw [Nat.mul_add]
    _ = ((b * d + k * d) + (b + k) * l) + b * d := by rw [nat_add_mul_pure]
    _ = ((b * d + k * d) + (b * l + k * l)) + b * d := by rw [nat_add_mul_pure]
    _ = ((b * d + k * d) + (b * d + b * l)) + k * l :=
      nat_add_perm_four (b * d) (k * d) (b * l) (k * l)
    _ = ((b * d + k * d) + b * (d + l)) + k * l := by rw [Nat.mul_add]
    _ = ((b + k) * d + b * (d + l)) + k * l := by rw [nat_add_mul_pure]

private theorem diffNorm_eq_ofNat_common (b k : Nat) : diffNorm (b + k) b = _root_.Int.ofNat k := by
  induction b with
  | zero =>
      rw [Nat.zero_add]
      exact diffNorm_zero_right k
  | succ b ih =>
      rw [Nat.succ_add]
      change diffNorm (b + k) b = _root_.Int.ofNat k
      exact ih

private theorem diffNorm_self (a : Nat) : diffNorm a a = 0 := by
  induction a with
  | zero =>
      rfl
  | succ _ ih =>
      exact ih

private theorem diffNorm_eq_negSucc_common (a k : Nat) :
    diffNorm a (a + k + 1) = _root_.Int.negSucc k := by
  induction a with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ a ih =>
      rw [Nat.succ_add]
      change diffNorm a (a + k + 1) = _root_.Int.negSucc k
      exact ih

private theorem diffNorm_eq_neg_ofNat_common (a k : Nat) :
    diffNorm a (a + k) = -_root_.Int.ofNat k := by
  cases k with
  | zero =>
      rw [Nat.add_zero]
      exact diffNorm_self a
  | succ k =>
      change diffNorm a (a + Nat.succ k) = _root_.Int.negSucc k
      rw [Nat.add_succ]
      exact diffNorm_eq_negSucc_common a k

private theorem diffNorm_pos_pos_mul (b k d l : Nat) :
    diffNorm (b + k) b * diffNorm (d + l) d =
      _root_.Int.ofNat k * _root_.Int.ofNat l := by
  calc
    diffNorm (b + k) b * diffNorm (d + l) d
        = _root_.Int.ofNat k * diffNorm (d + l) d := by
          rw [diffNorm_eq_ofNat_common b k]
    _ = _root_.Int.ofNat k * _root_.Int.ofNat l := by
          rw [diffNorm_eq_ofNat_common d l]

private theorem diffNorm_pos_neg_mul (b k c l : Nat) :
    diffNorm (b + k) b * diffNorm c (c + l + 1) =
      _root_.Int.ofNat k * _root_.Int.negSucc l := by
  calc
    diffNorm (b + k) b * diffNorm c (c + l + 1)
        = _root_.Int.ofNat k * diffNorm c (c + l + 1) := by
          rw [diffNorm_eq_ofNat_common b k]
    _ = _root_.Int.ofNat k * _root_.Int.negSucc l := by
          rw [diffNorm_eq_negSucc_common c l]

private theorem diffNorm_neg_pos_mul (a k d l : Nat) :
    diffNorm a (a + k + 1) * diffNorm (d + l) d =
      _root_.Int.negSucc k * _root_.Int.ofNat l := by
  calc
    diffNorm a (a + k + 1) * diffNorm (d + l) d
        = _root_.Int.negSucc k * diffNorm (d + l) d := by
          rw [diffNorm_eq_negSucc_common a k]
    _ = _root_.Int.negSucc k * _root_.Int.ofNat l := by
          rw [diffNorm_eq_ofNat_common d l]

private theorem diffNorm_neg_neg_mul (a k c l : Nat) :
    diffNorm a (a + k + 1) * diffNorm c (c + l + 1) =
      _root_.Int.negSucc k * _root_.Int.negSucc l := by
  calc
    diffNorm a (a + k + 1) * diffNorm c (c + l + 1)
        = _root_.Int.negSucc k * diffNorm c (c + l + 1) := by
          rw [diffNorm_eq_negSucc_common a k]
    _ = _root_.Int.negSucc k * _root_.Int.negSucc l := by
          rw [diffNorm_eq_negSucc_common c l]

private theorem diffNorm_mul (a b c d : Nat) :
    diffNorm (a * c + b * d) (a * d + b * c) = diffNorm a b * diffNorm c d := by
  cases hv : diffNorm a b with
  | ofNat k =>
      have aEq : a = b + k := diffNorm_ofNat_spec hv
      cases hw : diffNorm c d with
      | ofNat l =>
          have cEq : c = d + l := diffNorm_ofNat_spec hw
          rw [aEq, cEq]
          calc
            diffNorm ((b + k) * (d + l) + b * d) ((b + k) * d + b * (d + l))
                = diffNorm (((b + k) * d + b * (d + l)) + k * l)
                    ((b + k) * d + b * (d + l)) := by
                  rw [nat_mul_cross_nonneg b k d l]
            _ = _root_.Int.ofNat (k * l) :=
                  diffNorm_eq_ofNat_common ((b + k) * d + b * (d + l)) (k * l)
            _ = _root_.Int.ofNat k * _root_.Int.ofNat l :=
                  (_root_.Int.ofNat_mul_ofNat k l).symm
      | negSucc l =>
          have dEq : d = c + l + 1 := diffNorm_negSucc_spec hw
          rw [aEq, dEq]
          calc
            diffNorm ((b + k) * c + b * (c + l + 1))
                ((b + k) * (c + l + 1) + b * c)
                = diffNorm ((b + k) * c + b * (c + l + 1))
                    (((b + k) * c + b * (c + l + 1)) + k * (l + 1)) := by
                  rw [Nat.add_assoc c l 1]
                  rw [nat_mul_cross_nonneg b k c (l + 1)]
            _ = -_root_.Int.ofNat (k * (l + 1)) :=
                  diffNorm_eq_neg_ofNat_common ((b + k) * c + b * (c + l + 1))
                    (k * (l + 1))
            _ = _root_.Int.ofNat k * _root_.Int.negSucc l :=
                  (_root_.Int.ofNat_mul_negSucc k l).symm
  | negSucc k =>
      have bEq : b = a + k + 1 := diffNorm_negSucc_spec hv
      cases hw : diffNorm c d with
      | ofNat l =>
          have cEq : c = d + l := diffNorm_ofNat_spec hw
          rw [bEq, cEq]
          calc
            diffNorm (a * (d + l) + (a + k + 1) * d)
                (a * d + (a + k + 1) * (d + l))
                = diffNorm ((a + (k + 1)) * d + a * (d + l))
                    (((a + (k + 1)) * d + a * (d + l)) + (k + 1) * l) := by
                  rw [Nat.add_assoc a k 1]
                  rw [Nat.add_comm (a * (d + l)) ((a + (k + 1)) * d)]
                  rw [Nat.add_comm (a * d) ((a + (k + 1)) * (d + l))]
                  rw [nat_mul_cross_nonneg a (k + 1) d l]
            _ = -_root_.Int.ofNat ((k + 1) * l) :=
                  diffNorm_eq_neg_ofNat_common ((a + (k + 1)) * d + a * (d + l))
                    ((k + 1) * l)
            _ = _root_.Int.negSucc k * _root_.Int.ofNat l :=
                  (_root_.Int.negSucc_mul_ofNat k l).symm
      | negSucc l =>
          have dEq : d = c + l + 1 := diffNorm_negSucc_spec hw
          rw [bEq, dEq]
          calc
            diffNorm (a * c + (a + k + 1) * (c + l + 1))
                (a * (c + l + 1) + (a + k + 1) * c)
                = diffNorm (((a + (k + 1)) * c + a * (c + (l + 1))) + (k + 1) * (l + 1))
                    ((a + (k + 1)) * c + a * (c + (l + 1))) := by
                  rw [Nat.add_assoc a k 1, Nat.add_assoc c l 1]
                  rw [Nat.add_comm (a * c) ((a + (k + 1)) * (c + (l + 1)))]
                  rw [Nat.add_comm (a * (c + (l + 1))) ((a + (k + 1)) * c)]
                  rw [nat_mul_cross_nonneg a (k + 1) c (l + 1)]
            _ = _root_.Int.ofNat ((k + 1) * (l + 1)) :=
                  diffNorm_eq_ofNat_common ((a + (k + 1)) * c + a * (c + (l + 1)))
                    ((k + 1) * (l + 1))
            _ = _root_.Int.ofNat (Nat.succ k) * _root_.Int.ofNat (Nat.succ l) :=
                  (_root_.Int.ofNat_mul_ofNat (Nat.succ k) (Nat.succ l)).symm
            _ = _root_.Int.negSucc k * _root_.Int.negSucc l :=
                  (_root_.Int.negSucc_mul_negSucc k l).symm

private theorem cross_to_diff {a b c d : Nat}
    (h : a + d = c + b) :
    ((a : _root_.Int) - (b : _root_.Int)) =
      ((c : _root_.Int) - (d : _root_.Int)) := by
  rw [diff_eq_subNatNat a b, diff_eq_subNatNat c d]
  have h1 :
      _root_.Int.subNatNat (a + d) (b + d) =
        _root_.Int.subNatNat (c + b) (d + b) := by
    rw [h]
    rw [Nat.add_comm d b]
  rw [subNatNat_add_add_local a b d] at h1
  rw [subNatNat_add_add_local c d b] at h1
  exact h1

private theorem diff_to_cross {a b c d : Nat}
    (h : ((a : _root_.Int) - (b : _root_.Int)) =
      ((c : _root_.Int) - (d : _root_.Int))) : a + d = c + b := by
  rw [diff_eq_subNatNat a b, diff_eq_subNatNat c d] at h
  rw [subNatNat_eq_diffNorm a b, subNatNat_eq_diffNorm c d] at h
  exact diffNorm_eq_cross h

def natToUnary : Nat -> BHist
  | 0 => BHist.Empty
  | n + 1 => BHist.e1 (natToUnary n)

private theorem natToUnary_unary (n : Nat) : UnaryHistory (natToUnary n) := by
  induction n with
  | zero =>
      exact unary_empty
  | succ _ ih =>
      exact unary_e1_closed ih

private theorem natToUnary_length (n : Nat) : bwordLength (natToUnary n) = n := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨emptyLength, succLength, _noZero, _sameIff, _contAdd⟩
  induction n with
  | zero =>
      exact emptyLength
  | succ n ih =>
      change bwordLength (BHist.e1 (natToUnary n)) = Nat.succ n
      rw [succLength (natToUnary n) (natToUnary_unary n), ih]

def ofInt (z : _root_.Int) : BHist × BHist :=
  match z with
  | _root_.Int.ofNat n => (natToUnary n, BHist.Empty)
  | _root_.Int.negSucc n => (BHist.Empty, natToUnary (Nat.succ n))

private theorem ofInt_carrier (z : _root_.Int) :
    BEDC.Derived.IntUp.IntPairCarrier (ofInt z).1 (ofInt z).2 := by
  cases z with
  | ofNat n =>
      exact ⟨natToUnary_unary n, unary_empty⟩
  | negSucc n =>
      exact ⟨unary_empty, natToUnary_unary (Nat.succ n)⟩

theorem relIff {p n q m : BHist}
    (hp : UnaryHistory p) (hn : UnaryHistory n)
    (hq : UnaryHistory q) (hm : UnaryHistory m) :
    BEDC.Derived.IntUp.IntPairClassifier (p, n) (q, m) <->
      toInt (p, n) = toInt (q, m) := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨_emptyLength, _succLength, _noZero, sameIff, _contAdd⟩
  constructor
  · intro classified
    have leftUnary : UnaryHistory (append p m) :=
      unary_append_closed hp hm
    have rightUnary : UnaryHistory (append q n) :=
      unary_append_closed hq hn
    have lengthEq :
        bwordLength (append p m) = bwordLength (append q n) :=
      (sameIff leftUnary rightUnary).mp classified.right.right
    have cross :
        bwordLength p + bwordLength m = bwordLength q + bwordLength n := by
      rw [bwordLength_append p m, bwordLength_append q n] at lengthEq
      exact lengthEq
    unfold toInt
    change (bwordLength p : _root_.Int) - (bwordLength n : _root_.Int) =
      (bwordLength q : _root_.Int) - (bwordLength m : _root_.Int)
    exact cross_to_diff cross
  · intro intEq
    constructor
    · exact ⟨hp, hn⟩
    · constructor
      · exact ⟨hq, hm⟩
      · have cross :
            bwordLength p + bwordLength m = bwordLength q + bwordLength n := by
          unfold toInt at intEq
          change (bwordLength p : _root_.Int) - (bwordLength n : _root_.Int) =
            (bwordLength q : _root_.Int) - (bwordLength m : _root_.Int) at intEq
          exact diff_to_cross intEq
        have lengthEq :
            bwordLength (append p m) = bwordLength (append q n) := by
          rw [bwordLength_append p m, bwordLength_append q n]
          exact cross
        exact (sameIff (unary_append_closed hp hm) (unary_append_closed hq hn)).mpr
          lengthEq

theorem rightInv (z : _root_.Int) : toInt (ofInt z) = z := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨emptyLength, _succLength, _noZero, _sameIff, _contAdd⟩
  cases z with
  | ofNat n =>
      unfold ofInt toInt
      rw [natToUnary_length n, emptyLength]
      exact intSubZeroNat n
  | negSucc n =>
      unfold ofInt toInt
      rw [natToUnary_length (Nat.succ n), emptyLength]
      rfl

theorem leftInvRel {p n : BHist}
    (carrier : BEDC.Derived.IntUp.IntPairCarrier p n) :
    BEDC.Derived.IntUp.IntPairClassifier (ofInt (toInt (p, n))) (p, n) := by
  have sourceCarrier := ofInt_carrier (toInt (p, n))
  exact (relIff
    (p := (ofInt (toInt (p, n))).1)
    (n := (ofInt (toInt (p, n))).2)
    (q := p)
    (m := n)
    sourceCarrier.left
    sourceCarrier.right
    carrier.left
    carrier.right).mpr (rightInv (toInt (p, n)))

def intRelQuotEquiv :
    BedcMathlibBridge.RelQuotEquiv
      {x : BHist × BHist // BEDC.Derived.IntUp.IntPairCarrier x.1 x.2}
      (fun a b => BEDC.Derived.IntUp.IntPairClassifier a.val b.val)
      _root_.Int where
  toM := fun a => toInt a.val
  ofM := fun z => ⟨ofInt z, ofInt_carrier z⟩
  leftInvRel := by
    intro a
    rcases a with ⟨⟨p, n⟩, carrier⟩
    exact leftInvRel carrier
  rightInv := by
    intro z
    exact rightInv z
  relIff := by
    intro a b
    rcases a with ⟨⟨p, n⟩, carrierA⟩
    rcases b with ⟨⟨q, m⟩, carrierB⟩
    exact relIff carrierA.left carrierA.right carrierB.left carrierB.right

def pairAdd (x y : BHist × BHist) : BHist × BHist :=
  (append x.1 y.1, append x.2 y.2)

def pairNeg (x : BHist × BHist) : BHist × BHist :=
  (x.2, x.1)

theorem natMul_bwordLength {d q n : BHist} :
    BEDC.Derived.PrimeUp.NatMul d q n ->
      bwordLength n = bwordLength d * bwordLength q := by
  intro mul
  induction mul with
  | zero _hd =>
      exact (Nat.mul_zero (bwordLength d)).symm
  | succ previous step ih =>
      calc
        bwordLength _ = bwordLength (BEDC.FKernel.Cont.append _ d) := congrArg bwordLength step
        _ = bwordLength _ + bwordLength d := bwordLength_append _ d
        _ = bwordLength d * bwordLength _ + bwordLength d :=
          congrArg (fun x => x + bwordLength d) ih
        _ = bwordLength d * Nat.succ (bwordLength _) :=
          (Nat.mul_succ (bwordLength d) (bwordLength _)).symm

def natMulFn (d : BHist) : BHist -> BHist
  | BHist.Empty => BHist.Empty
  | BHist.e0 _ => BHist.Empty
  | BHist.e1 q => append (natMulFn d q) d

theorem natMulFn_unary {d q : BHist} :
    UnaryHistory d -> UnaryHistory q -> UnaryHistory (natMulFn d q) := by
  intro hd hq
  induction q with
  | Empty =>
      exact unary_empty
  | e0 _ =>
      cases hq
  | e1 q ih =>
      exact unary_append_closed (ih hq) hd

theorem natMulFn_rel {d q : BHist} :
    UnaryHistory d -> UnaryHistory q -> BEDC.Derived.PrimeUp.NatMul d q (natMulFn d q) := by
  intro hd hq
  induction q with
  | Empty =>
      exact BEDC.Derived.PrimeUp.NatMul.zero hd
  | e0 _ =>
      cases hq
  | e1 q ih =>
      exact BEDC.Derived.PrimeUp.NatMul.succ (ih hq) (BEDC.FKernel.Cont.cont_intro rfl)

theorem natMulFn_bwordLength {d q : BHist} :
    UnaryHistory d -> UnaryHistory q ->
      bwordLength (natMulFn d q) = bwordLength d * bwordLength q := by
  intro hd hq
  exact natMul_bwordLength (natMulFn_rel hd hq)

def pairMul (x y : BHist × BHist) : BHist × BHist :=
  (append (natMulFn x.1 y.1) (natMulFn x.2 y.2),
    append (natMulFn x.1 y.2) (natMulFn x.2 y.1))

def pairLe (x y : BHist × BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧
    BEDC.FKernel.Cont.Cont (append x.1 y.2) tail (append y.1 x.2)

theorem pairMul_carrier {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    BEDC.Derived.IntUp.IntPairCarrier (pairMul x y).1 (pairMul x y).2 := by
  rcases x with ⟨p, n⟩
  rcases y with ⟨q, m⟩
  exact
    ⟨unary_append_closed (natMulFn_unary hx.left hy.left) (natMulFn_unary hx.right hy.right),
      unary_append_closed (natMulFn_unary hx.left hy.right) (natMulFn_unary hx.right hy.left)⟩

theorem pairLe_reflects_length_order {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y ->
      ∃ k : Nat,
        bwordLength y.1 + bwordLength x.2 =
          bwordLength x.1 + bwordLength y.2 + k := by
  intro hle
  rcases hle with ⟨tail, tailUnary, cont⟩
  refine ⟨bwordLength tail, ?_⟩
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  have sourceUnary : UnaryHistory (append x.1 y.2) := unary_append_closed hx.left hy.right
  have lengthEq := bridge.right.right.right.right sourceUnary tailUnary cont
  rw [bwordLength_append y.1 x.2] at lengthEq
  rw [bwordLength_append x.1 y.2] at lengthEq
  exact lengthEq

theorem pairLe_total {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    pairLe x y ∨ pairLe y x := by
  have leftUnary : UnaryHistory (append x.1 y.2) := unary_append_closed hx.left hy.right
  have rightUnary : UnaryHistory (append y.1 x.2) := unary_append_closed hy.left hx.right
  cases BEDC.Derived.NatUp.NatUnaryPrefix_total leftUnary rightUnary with
  | inl left =>
      exact Or.inl left
  | inr right =>
      exact Or.inr right

theorem pairAdd_toInt {x y : BHist × BHist}
    (_hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (_hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    toInt (pairAdd x y) = toInt x + toInt y := by
  rcases x with ⟨p, n⟩
  rcases y with ⟨q, m⟩
  unfold pairAdd toInt
  change (bwordLength (append p q) : _root_.Int) -
      (bwordLength (append n m) : _root_.Int) =
    ((bwordLength p : _root_.Int) - (bwordLength n : _root_.Int)) +
      ((bwordLength q : _root_.Int) - (bwordLength m : _root_.Int))
  rw [bwordLength_append p q, bwordLength_append n m]
  rw [diff_eq_subNatNat (bwordLength p + bwordLength q) (bwordLength n + bwordLength m)]
  rw [diff_eq_subNatNat (bwordLength p) (bwordLength n)]
  rw [diff_eq_subNatNat (bwordLength q) (bwordLength m)]
  rw [subNatNat_eq_diffNorm (bwordLength p + bwordLength q)
    (bwordLength n + bwordLength m)]
  rw [subNatNat_eq_diffNorm (bwordLength p) (bwordLength n)]
  rw [subNatNat_eq_diffNorm (bwordLength q) (bwordLength m)]
  exact (diffNorm_add (bwordLength p) (bwordLength n) (bwordLength q) (bwordLength m)).symm

theorem pairNeg_toInt (x : BHist × BHist) :
    toInt (pairNeg x) = -toInt x := by
  rcases x with ⟨p, n⟩
  unfold pairNeg toInt
  rw [diff_eq_subNatNat (bwordLength n) (bwordLength p)]
  rw [diff_eq_subNatNat (bwordLength p) (bwordLength n)]
  rw [subNatNat_eq_diffNorm (bwordLength n) (bwordLength p)]
  rw [subNatNat_eq_diffNorm (bwordLength p) (bwordLength n)]
  exact diffNorm_neg (bwordLength p) (bwordLength n)

theorem pairMul_toInt {x y : BHist × BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2)
    (hy : BEDC.Derived.IntUp.IntPairCarrier y.1 y.2) :
    toInt (pairMul x y) = toInt x * toInt y := by
  rcases x with ⟨p, n⟩
  rcases y with ⟨q, m⟩
  unfold pairMul toInt
  rw [bwordLength_append (natMulFn p q) (natMulFn n m)]
  rw [bwordLength_append (natMulFn p m) (natMulFn n q)]
  rw [natMulFn_bwordLength hx.left hy.left]
  rw [natMulFn_bwordLength hx.right hy.right]
  rw [natMulFn_bwordLength hx.left hy.right]
  rw [natMulFn_bwordLength hx.right hy.left]
  rw [diff_eq_subNatNat (bwordLength p * bwordLength q + bwordLength n * bwordLength m)
    (bwordLength p * bwordLength m + bwordLength n * bwordLength q)]
  rw [diff_eq_subNatNat (bwordLength p) (bwordLength n)]
  rw [diff_eq_subNatNat (bwordLength q) (bwordLength m)]
  rw [subNatNat_eq_diffNorm
    (bwordLength p * bwordLength q + bwordLength n * bwordLength m)
    (bwordLength p * bwordLength m + bwordLength n * bwordLength q)]
  rw [subNatNat_eq_diffNorm (bwordLength p) (bwordLength n)]
  rw [subNatNat_eq_diffNorm (bwordLength q) (bwordLength m)]
  exact diffNorm_mul (bwordLength p) (bwordLength n) (bwordLength q) (bwordLength m)

theorem zero_toInt : toInt (BHist.Empty, BHist.Empty) = 0 := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨emptyLength, _succLength, _noZero, _sameIff, _contAdd⟩
  unfold toInt
  rw [emptyLength]
  rfl

def IsCanonical (x : BHist × BHist) : Prop :=
  x = ofInt (toInt x)

def CInt : Type :=
  {x : BHist × BHist // BEDC.Derived.IntUp.IntPairCarrier x.1 x.2 ∧ IsCanonical x}

def normalize (x : BHist × BHist) : CInt :=
  ⟨ofInt (toInt x), ofInt_carrier (toInt x), by
    unfold IsCanonical
    rw [rightInv]⟩

def CInt.ofInt (z : _root_.Int) : CInt :=
  ⟨BedcMathlibBridge.Constructive.Int.ofInt z, ofInt_carrier z, by
    unfold IsCanonical
    rw [rightInv]⟩

def CInt.toInt (x : CInt) : _root_.Int :=
  BedcMathlibBridge.Constructive.Int.toInt x.val

theorem CInt.toInt_ofInt (z : _root_.Int) : (CInt.ofInt z).toInt = z := by
  exact rightInv z

theorem CInt.ofInt_toInt (x : CInt) : CInt.ofInt x.toInt = x := by
  rcases x with ⟨x, carrier, canonical⟩
  apply Subtype.ext
  change BedcMathlibBridge.Constructive.Int.ofInt
      (BedcMathlibBridge.Constructive.Int.toInt x) = x
  exact canonical.symm

theorem CInt.canonical_ext {x y : CInt} (h : x.toInt = y.toInt) : x = y := by
  calc
    x = CInt.ofInt x.toInt := (CInt.ofInt_toInt x).symm
    _ = CInt.ofInt y.toInt := by rw [h]
    _ = y := CInt.ofInt_toInt y

instance : Zero CInt where
  zero := CInt.ofInt 0

instance : Add CInt where
  add x y := normalize (pairAdd x.val y.val)

instance : Neg CInt where
  neg x := normalize (pairNeg x.val)

instance : Sub CInt where
  sub x y := x + -y

instance : One CInt where
  one := CInt.ofInt 1

instance : Mul CInt where
  mul x y := normalize (pairMul x.val y.val)

theorem CInt.toInt_zero : (0 : CInt).toInt = 0 := by
  exact CInt.toInt_ofInt 0

theorem CInt.toInt_one : (1 : CInt).toInt = 1 := by
  exact CInt.toInt_ofInt 1

theorem CInt.toInt_add (x y : CInt) : (x + y).toInt = x.toInt + y.toInt := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change BedcMathlibBridge.Constructive.Int.toInt
      (BedcMathlibBridge.Constructive.Int.ofInt
        (BedcMathlibBridge.Constructive.Int.toInt (pairAdd x y))) =
    BedcMathlibBridge.Constructive.Int.toInt x + BedcMathlibBridge.Constructive.Int.toInt y
  rw [rightInv]
  exact pairAdd_toInt hx.left hy.left

theorem CInt.toInt_neg (x : CInt) : (-x).toInt = -x.toInt := by
  rcases x with ⟨x, _hx⟩
  change BedcMathlibBridge.Constructive.Int.toInt
      (BedcMathlibBridge.Constructive.Int.ofInt
        (BedcMathlibBridge.Constructive.Int.toInt (pairNeg x))) =
    -BedcMathlibBridge.Constructive.Int.toInt x
  rw [rightInv]
  exact pairNeg_toInt x

theorem CInt.toInt_sub (x y : CInt) : (x - y).toInt = x.toInt - y.toInt := by
  change (x + -y).toInt = x.toInt - y.toInt
  rw [CInt.toInt_add, CInt.toInt_neg]
  rfl

theorem CInt.toInt_mul (x y : CInt) : (x * y).toInt = x.toInt * y.toInt := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  change BedcMathlibBridge.Constructive.Int.toInt
      (BedcMathlibBridge.Constructive.Int.ofInt
        (BedcMathlibBridge.Constructive.Int.toInt (pairMul x y))) =
    BedcMathlibBridge.Constructive.Int.toInt x * BedcMathlibBridge.Constructive.Int.toInt y
  rw [rightInv]
  exact pairMul_toInt hx.left hy.left

def CInt.toIntEquiv : CInt ≃ _root_.Int where
  toFun := CInt.toInt
  invFun := CInt.ofInt
  left_inv := CInt.ofInt_toInt
  right_inv := CInt.toInt_ofInt

def CInt.toIntAddEquiv : CInt ≃+ _root_.Int :=
  AddEquiv.mk CInt.toIntEquiv CInt.toInt_add

def CInt.toIntRingEquiv : CInt ≃+* _root_.Int :=
  RingEquiv.mk CInt.toIntEquiv CInt.toInt_mul CInt.toInt_add

end BedcMathlibBridge.Constructive.Int
