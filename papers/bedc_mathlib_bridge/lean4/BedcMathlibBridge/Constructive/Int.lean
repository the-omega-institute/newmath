import BEDC.Derived.IntUp
import BEDC.Derived.NatUp
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Unary
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

theorem zero_toInt : toInt (BHist.Empty, BHist.Empty) = 0 := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨emptyLength, _succLength, _noZero, _sameIff, _contAdd⟩
  unfold toInt
  rw [emptyLength]
  rfl

end BedcMathlibBridge.Constructive.Int
