import BEDC.Real.RatInterval

namespace BEDC.Real.RatLogEnclosure

open BEDC.Real.RatInterval

abbrev Q : Type :=
  BEDC.Real.RatInterval.Rat

def atanhTerm (z : Q) (j : Nat) : Q :=
  z ^ (2 * j + 1) / ((2 * j + 1 : Nat) : Q)

def atanhPart (z : Q) (M : Nat) : Q :=
  sumN M (atanhTerm z)

def atanhTail (z : Q) (M : Nat) : Q :=
  z ^ (2 * M + 1) /
    (((2 * M + 1 : Nat) : Q) * (1 - z * z))

def atanhFiniteTail (z : Q) (M K : Nat) : Q :=
  sumN K (fun j =>
    z ^ (2 * (M + j) + 1) / ((2 * (M + j) + 1 : Nat) : Q))

def twoAtanhLo (z : Q) (M : Nat) : Q :=
  2 * atanhPart z M

def twoAtanhHi (z : Q) (M : Nat) : Q :=
  2 * (atanhPart z M + atanhTail z M)

structure AtanhTailKernel (α : Type u) where
  zero : α
  add : α -> α -> α
  le : α -> α -> Prop
  term : Nat -> α
  tail : Nat -> α
  tailDenomPos : Nat -> Prop
  tailDenomPos_holds : ∀ m, tailDenomPos m
  zero_add_tail : ∀ m, le (add zero (tail m)) (tail m)
  add_assoc_left : ∀ a b c d, le (add a (add b c)) d -> le (add (add a b) c) d
  add_left_mono : ∀ a b c, le b c -> le (add a b) (add a c)
  le_trans : ∀ a b c, le a b -> le b c -> le a c
  zero_le_zero : le zero zero
  term_nonneg : ∀ m, le zero (term m)
  tail_nonneg : ∀ m, le zero (tail m)
  add_nonneg : ∀ a b, le zero a -> le zero b -> le zero (add a b)
  add_right_nonneg : ∀ a b, le zero b -> le a (add a b)
  tail_step : ∀ m, tailDenomPos m -> tailDenomPos (m + 1) ->
    le (add (term m) (tail (m + 1))) (tail m)

namespace AtanhTailKernel

def finiteTail {α : Type u} (K : AtanhTailKernel α) (M : Nat) : Nat -> α
  | 0 => K.zero
  | Nat.succ n => K.add (K.term M) (finiteTail K (M + 1) n)

theorem finiteTail_nonneg {α : Type u}
    (K : AtanhTailKernel α) (M L : Nat) :
    K.le K.zero (finiteTail K M L) := by
  induction L generalizing M with
  | zero =>
      exact K.zero_le_zero
  | succ L ih =>
      change K.le K.zero (K.add (K.term M) (finiteTail K (M + 1) L))
      exact K.add_nonneg (K.term M) (finiteTail K (M + 1) L)
        (K.term_nonneg M) (ih (M + 1))

theorem finiteTail_with_remaining_le_tail {α : Type u}
    (K : AtanhTailKernel α) (M L : Nat) :
    K.le (K.add (finiteTail K M L) (K.tail (M + L))) (K.tail M) := by
  induction L generalizing M with
  | zero =>
      change K.le (K.add K.zero (K.tail (M + 0))) (K.tail M)
      rw [Nat.add_zero]
      exact K.zero_add_tail M
  | succ L ih =>
      change K.le
        (K.add (K.add (K.term M) (finiteTail K (M + 1) L))
          (K.tail (M + Nat.succ L)))
        (K.tail M)
      have h_index : M + Nat.succ L = (M + 1) + L := by
        rw [Nat.add_succ]
        rw [Nat.succ_add]
      rw [h_index]
      apply K.add_assoc_left
      have h_ih :
          K.le (K.add (finiteTail K (M + 1) L) (K.tail ((M + 1) + L)))
            (K.tail (M + 1)) :=
        ih (M + 1)
      have h_mono :
          K.le
            (K.add (K.term M)
              (K.add (finiteTail K (M + 1) L) (K.tail ((M + 1) + L))))
            (K.add (K.term M) (K.tail (M + 1))) :=
        K.add_left_mono (K.term M)
          (K.add (finiteTail K (M + 1) L) (K.tail ((M + 1) + L)))
          (K.tail (M + 1)) h_ih
      exact K.le_trans
        (K.add (K.term M)
          (K.add (finiteTail K (M + 1) L) (K.tail ((M + 1) + L))))
        (K.add (K.term M) (K.tail (M + 1)))
        (K.tail M) h_mono
        (K.tail_step M (K.tailDenomPos_holds M) (K.tailDenomPos_holds (M + 1)))

theorem finiteTail_le_tail {α : Type u}
    (K : AtanhTailKernel α) (M L : Nat) :
    K.le (finiteTail K M L) (K.tail M) := by
  have h_start :
      K.le (finiteTail K M L) (K.add (finiteTail K M L) (K.tail (M + L))) :=
    K.add_right_nonneg (finiteTail K M L) (K.tail (M + L)) (K.tail_nonneg (M + L))
  exact K.le_trans (finiteTail K M L)
    (K.add (finiteTail K M L) (K.tail (M + L)))
    (K.tail M) h_start (finiteTail_with_remaining_le_tail K M L)

end AtanhTailKernel

def atanhFiniteTailF {α : Type u} (K : AtanhTailKernel α) (M L : Nat) : α :=
  AtanhTailKernel.finiteTail K M L

def atanhTailF {α : Type u} (K : AtanhTailKernel α) (M : Nat) : α :=
  K.tail M

theorem atanhFiniteTailF_with_remaining_le_tailF {α : Type u}
    (K : AtanhTailKernel α) (M L : Nat) :
    K.le (K.add (atanhFiniteTailF K M L) (atanhTailF K (M + L))) (atanhTailF K M) :=
  AtanhTailKernel.finiteTail_with_remaining_le_tail K M L

theorem atanhFiniteTailF_le_tailF {α : Type u}
    (K : AtanhTailKernel α) (M L : Nat) :
    K.le (atanhFiniteTailF K M L) (atanhTailF K M) :=
  AtanhTailKernel.finiteTail_le_tail K M L

structure AtanhPartTailKernel (α : Type u) extends AtanhTailKernel α where
  part : Nat -> α
  part_add_finiteTail : ∀ M L,
    part (M + L) = add (part M) (AtanhTailKernel.finiteTail toAtanhTailKernel M L)

def atanhPartF {α : Type u} (K : AtanhPartTailKernel α) (M : Nat) : α :=
  K.part M

theorem atanhPartF_future_enclosed {α : Type u}
    (K : AtanhPartTailKernel α) (M L : Nat) :
    K.le (atanhPartF K M) (atanhPartF K (M + L)) ∧
      K.le (atanhPartF K (M + L)) (K.add (atanhPartF K M) (K.tail M)) := by
  constructor
  · unfold atanhPartF
    rw [K.part_add_finiteTail M L]
    exact K.add_right_nonneg (K.part M)
      (AtanhTailKernel.finiteTail K.toAtanhTailKernel M L)
      (AtanhTailKernel.finiteTail_nonneg K.toAtanhTailKernel M L)
  · unfold atanhPartF
    rw [K.part_add_finiteTail M L]
    exact K.add_left_mono (K.part M)
      (AtanhTailKernel.finiteTail K.toAtanhTailKernel M L)
      (K.tail M)
      (atanhFiniteTailF_le_tailF K.toAtanhTailKernel M L)

structure AtanhFiniteTailSmokeCert where
  z : Q
  M : Nat
  K : Nat

namespace AtanhFiniteTailSmokeCert

def check (c : AtanhFiniteTailSmokeCert) : Bool :=
  qLeBool 0 c.z &&
    (qLtBool c.z 1 &&
      (qLtBool 0 (1 - c.z * c.z) &&
        qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M)))

def Sound (c : AtanhFiniteTailSmokeCert) : Prop :=
  (0 : Q) <= c.z ∧
    c.z < 1 ∧
      (0 : Q) < 1 - c.z * c.z ∧
        atanhFiniteTail c.z c.M c.K <= atanhTail c.z c.M

end AtanhFiniteTailSmokeCert

theorem atanhFiniteTail_cert_bound {z : Q} {M K : Nat}
    (hfinite : qLeBool (atanhFiniteTail z M K) (atanhTail z M) = true) :
    atanhFiniteTail z M K <= atanhTail z M := by
  exact qLe_of_qLeBool hfinite

theorem atanhFiniteTailSmokeCert_sound (c : AtanhFiniteTailSmokeCert) :
    AtanhFiniteTailSmokeCert.check c = true -> AtanhFiniteTailSmokeCert.Sound c := by
  intro h
  unfold AtanhFiniteTailSmokeCert.check at h
  have h_nonneg_bool :
      qLeBool 0 c.z = true :=
    boolAndLeftTrue h
  have h_rest :
      (qLtBool c.z 1 &&
        (qLtBool 0 (1 - c.z * c.z) &&
          qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M))) = true :=
    boolAndRightTrue h
  have h_lt_bool :
      qLtBool c.z 1 = true :=
    boolAndLeftTrue h_rest
  have h_tail_bool :
      (qLtBool 0 (1 - c.z * c.z) &&
        qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M)) = true :=
    boolAndRightTrue h_rest
  have h_denom_pos_bool :
      qLtBool 0 (1 - c.z * c.z) = true :=
    boolAndLeftTrue h_tail_bool
  have h_tail_bound_bool :
      qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M) = true :=
    boolAndRightTrue h_tail_bool
  exact
    And.intro (qLe_of_qLeBool h_nonneg_bool)
      (And.intro (qLt_of_qLtBool h_lt_bool)
        (And.intro (qLt_of_qLtBool h_denom_pos_bool)
          (atanhFiniteTail_cert_bound h_tail_bound_bool)))

def sampleAtanhFiniteTailSmokeCert : AtanhFiniteTailSmokeCert :=
  { z := 1 / 3, M := 2, K := 3 }

theorem sampleAtanhFiniteTailSmokeCert_ok :
    AtanhFiniteTailSmokeCert.check sampleAtanhFiniteTailSmokeCert = true := by
  rfl

theorem sampleAtanhFiniteTailSmokeCert_sound :
    AtanhFiniteTailSmokeCert.Sound sampleAtanhFiniteTailSmokeCert :=
  atanhFiniteTailSmokeCert_sound sampleAtanhFiniteTailSmokeCert
    sampleAtanhFiniteTailSmokeCert_ok

def pow2 : Nat -> Nat
  | 0 => 1
  | Nat.succ n => 2 * pow2 n

def kLogSmall (n : Nat) : Nat :=
  if n < 2 then 0
  else if n < 4 then 1
  else if n < 8 then 2
  else 3

def zLogSmall (n : Nat) : Q :=
  let k := kLogSmall n
  (((n : Nat) : Q) - ((pow2 k : Nat) : Q)) /
    (((n : Nat) : Q) + ((pow2 k : Nat) : Q))

def logLoSmall (n M : Nat) : Q :=
  let k := kLogSmall n
  ((k : Nat) : Q) * twoAtanhLo (1 / 3) M +
    twoAtanhLo (zLogSmall n) M

def logHiSmall (n M : Nat) : Q :=
  let k := kLogSmall n
  ((k : Nat) : Q) * twoAtanhHi (1 / 3) M +
    twoAtanhHi (zLogSmall n) M

def logEnclosureLimit : Nat :=
  8

def logExampleM : Nat :=
  4

def logExampleTailK : Nat :=
  4

structure LogNatArithCert where
  n : Nat
  M : Nat
  K : Nat

namespace LogNatArithCert

def lnTwoTailCert (c : LogNatArithCert) : AtanhFiniteTailSmokeCert :=
  { z := 1 / 3, M := c.M, K := c.K }

def zTailCert (c : LogNatArithCert) : AtanhFiniteTailSmokeCert :=
  { z := zLogSmall c.n, M := c.M, K := c.K }

def check (c : LogNatArithCert) : Bool :=
    qLeBool 1 ((c.n : Nat) : Q) &&
    (qLeBool ((c.n : Nat) : Q) ((logEnclosureLimit : Nat) : Q) &&
      (AtanhFiniteTailSmokeCert.check (lnTwoTailCert c) &&
        (AtanhFiniteTailSmokeCert.check (zTailCert c) &&
          qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M))))

def Sound (c : LogNatArithCert) : Prop :=
  (1 : Q) <= ((c.n : Nat) : Q) ∧
    ((c.n : Nat) : Q) <= ((logEnclosureLimit : Nat) : Q) ∧
      AtanhFiniteTailSmokeCert.Sound (lnTwoTailCert c) ∧
        AtanhFiniteTailSmokeCert.Sound (zTailCert c) ∧
          logLoSmall c.n c.M <= logHiSmall c.n c.M

end LogNatArithCert

theorem logNat_arith_sound (c : LogNatArithCert) :
    LogNatArithCert.check c = true -> LogNatArithCert.Sound c := by
  intro h
  unfold LogNatArithCert.check at h
  have h_n_lower :
      qLeBool 1 ((c.n : Nat) : Q) = true :=
    boolAndLeftTrue h
  have h_after_lower :
      (qLeBool ((c.n : Nat) : Q) ((logEnclosureLimit : Nat) : Q) &&
        (AtanhFiniteTailSmokeCert.check (LogNatArithCert.lnTwoTailCert c) &&
          (AtanhFiniteTailSmokeCert.check (LogNatArithCert.zTailCert c) &&
            qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M)))) = true :=
    boolAndRightTrue h
  have h_n_upper :
      qLeBool ((c.n : Nat) : Q) ((logEnclosureLimit : Nat) : Q) = true :=
    boolAndLeftTrue h_after_lower
  have h_after_upper :
      (AtanhFiniteTailSmokeCert.check (LogNatArithCert.lnTwoTailCert c) &&
        (AtanhFiniteTailSmokeCert.check (LogNatArithCert.zTailCert c) &&
          qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M))) = true :=
    boolAndRightTrue h_after_lower
  have h_ln2 :
      AtanhFiniteTailSmokeCert.check (LogNatArithCert.lnTwoTailCert c) = true :=
    boolAndLeftTrue h_after_upper
  have h_after_ln2 :
      (AtanhFiniteTailSmokeCert.check (LogNatArithCert.zTailCert c) &&
        qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M)) = true :=
    boolAndRightTrue h_after_upper
  have h_z :
      AtanhFiniteTailSmokeCert.check (LogNatArithCert.zTailCert c) = true :=
    boolAndLeftTrue h_after_ln2
  have h_ordered :
      qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M) = true :=
    boolAndRightTrue h_after_ln2
  exact
    And.intro (qLe_of_qLeBool h_n_lower)
      (And.intro (qLe_of_qLeBool h_n_upper)
          (And.intro
          (atanhFiniteTailSmokeCert_sound (LogNatArithCert.lnTwoTailCert c) h_ln2)
          (And.intro
            (atanhFiniteTailSmokeCert_sound (LogNatArithCert.zTailCert c) h_z)
            (qLe_of_qLeBool h_ordered))))

def logNatCert1 : LogNatArithCert :=
  { n := 1, M := logExampleM, K := logExampleTailK }

def logNatCert2 : LogNatArithCert :=
  { n := 2, M := logExampleM, K := logExampleTailK }

def logNatCert3 : LogNatArithCert :=
  { n := 3, M := logExampleM, K := logExampleTailK }

def logNatCert4 : LogNatArithCert :=
  { n := 4, M := logExampleM, K := logExampleTailK }

def logNatCert5 : LogNatArithCert :=
  { n := 5, M := logExampleM, K := logExampleTailK }

def logNatCert6 : LogNatArithCert :=
  { n := 6, M := logExampleM, K := logExampleTailK }

def logNatCert7 : LogNatArithCert :=
  { n := 7, M := logExampleM, K := logExampleTailK }

def logNatCert8 : LogNatArithCert :=
  { n := 8, M := logExampleM, K := logExampleTailK }

theorem logNatCert1_ok :
    LogNatArithCert.check logNatCert1 = true := by
  rfl

theorem logNatCert2_ok :
    LogNatArithCert.check logNatCert2 = true := by
  rfl

theorem logNatCert3_ok :
    LogNatArithCert.check logNatCert3 = true := by
  rfl

theorem logNatCert4_ok :
    LogNatArithCert.check logNatCert4 = true := by
  rfl

theorem logNatCert5_ok :
    LogNatArithCert.check logNatCert5 = true := by
  rfl

theorem logNatCert6_ok :
    LogNatArithCert.check logNatCert6 = true := by
  rfl

theorem logNatCert7_ok :
    LogNatArithCert.check logNatCert7 = true := by
  rfl

theorem logNatCert8_ok :
    LogNatArithCert.check logNatCert8 = true := by
  rfl

theorem logNat1_arith_sound :
    LogNatArithCert.Sound logNatCert1 :=
  logNat_arith_sound logNatCert1 logNatCert1_ok

theorem logNat2_arith_sound :
    LogNatArithCert.Sound logNatCert2 :=
  logNat_arith_sound logNatCert2 logNatCert2_ok

theorem logNat3_arith_sound :
    LogNatArithCert.Sound logNatCert3 :=
  logNat_arith_sound logNatCert3 logNatCert3_ok

theorem logNat4_arith_sound :
    LogNatArithCert.Sound logNatCert4 :=
  logNat_arith_sound logNatCert4 logNatCert4_ok

theorem logNat5_arith_sound :
    LogNatArithCert.Sound logNatCert5 :=
  logNat_arith_sound logNatCert5 logNatCert5_ok

theorem logNat6_arith_sound :
    LogNatArithCert.Sound logNatCert6 :=
  logNat_arith_sound logNatCert6 logNatCert6_ok

theorem logNat7_arith_sound :
    LogNatArithCert.Sound logNatCert7 :=
  logNat_arith_sound logNatCert7 logNatCert7_ok

theorem logNat8_arith_sound :
    LogNatArithCert.Sound logNatCert8 :=
  logNat_arith_sound logNatCert8 logNatCert8_ok

structure LogTwoOverLogNatArithCert where
  target : LogNatArithCert

namespace LogTwoOverLogNatArithCert

def numerator (c : LogTwoOverLogNatArithCert) : LogNatArithCert :=
  { n := 2, M := c.target.M, K := c.target.K }

def lo (c : LogTwoOverLogNatArithCert) : Q :=
  logLoSmall 2 c.target.M / logHiSmall c.target.n c.target.M

def hi (c : LogTwoOverLogNatArithCert) : Q :=
  logHiSmall 2 c.target.M / logLoSmall c.target.n c.target.M

def check (c : LogTwoOverLogNatArithCert) : Bool :=
  LogNatArithCert.check (numerator c) &&
    (LogNatArithCert.check c.target &&
      (qLtBool 0 (logLoSmall c.target.n c.target.M) &&
        qLeBool (lo c) (hi c)))

def Sound (c : LogTwoOverLogNatArithCert) : Prop :=
  LogNatArithCert.Sound (numerator c) ∧
    LogNatArithCert.Sound c.target ∧
      (0 : Q) < logLoSmall c.target.n c.target.M ∧
        lo c <= hi c

theorem numerator_matches_target_M (c : LogTwoOverLogNatArithCert) :
    (numerator c).M = c.target.M := by
  rfl

end LogTwoOverLogNatArithCert

theorem logTwoOverLogNatArith_sound (c : LogTwoOverLogNatArithCert) :
    LogTwoOverLogNatArithCert.check c = true -> LogTwoOverLogNatArithCert.Sound c := by
  intro h
  unfold LogTwoOverLogNatArithCert.check at h
  have h_numerator :
      LogNatArithCert.check (LogTwoOverLogNatArithCert.numerator c) = true :=
    boolAndLeftTrue h
  have h_after_numerator :
      (LogNatArithCert.check c.target &&
        (qLtBool 0 (logLoSmall c.target.n c.target.M) &&
          qLeBool (LogTwoOverLogNatArithCert.lo c) (LogTwoOverLogNatArithCert.hi c))) = true :=
    boolAndRightTrue h
  have h_target :
      LogNatArithCert.check c.target = true :=
    boolAndLeftTrue h_after_numerator
  have h_after_target :
      (qLtBool 0 (logLoSmall c.target.n c.target.M) &&
        qLeBool (LogTwoOverLogNatArithCert.lo c) (LogTwoOverLogNatArithCert.hi c)) = true :=
    boolAndRightTrue h_after_numerator
  have h_positive :
      qLtBool 0 (logLoSmall c.target.n c.target.M) = true :=
    boolAndLeftTrue h_after_target
  have h_ordered :
      qLeBool (LogTwoOverLogNatArithCert.lo c) (LogTwoOverLogNatArithCert.hi c) = true :=
    boolAndRightTrue h_after_target
  exact
    And.intro (logNat_arith_sound (LogTwoOverLogNatArithCert.numerator c) h_numerator)
      (And.intro (logNat_arith_sound c.target h_target)
        (And.intro (qLt_of_qLtBool h_positive)
          (qLe_of_qLeBool h_ordered)))

def logTwoOverLogNatArithCert2 : LogTwoOverLogNatArithCert :=
  { target := logNatCert2 }

def logTwoOverLogNatArithCert3 : LogTwoOverLogNatArithCert :=
  { target := logNatCert3 }

def logTwoOverLogNatArithCert4 : LogTwoOverLogNatArithCert :=
  { target := logNatCert4 }

theorem logTwoOverLogNatArithCert2_ok :
    LogTwoOverLogNatArithCert.check logTwoOverLogNatArithCert2 = true := by
  rfl

theorem logTwoOverLogNatArithCert3_ok :
    LogTwoOverLogNatArithCert.check logTwoOverLogNatArithCert3 = true := by
  rfl

theorem logTwoOverLogNatArithCert4_ok :
    LogTwoOverLogNatArithCert.check logTwoOverLogNatArithCert4 = true := by
  rfl

theorem logTwoOverLogNat2_arith_sound :
    LogTwoOverLogNatArithCert.Sound logTwoOverLogNatArithCert2 :=
  logTwoOverLogNatArith_sound logTwoOverLogNatArithCert2
    logTwoOverLogNatArithCert2_ok

theorem logTwoOverLogNat3_arith_sound :
    LogTwoOverLogNatArithCert.Sound logTwoOverLogNatArithCert3 :=
  logTwoOverLogNatArith_sound logTwoOverLogNatArithCert3
    logTwoOverLogNatArithCert3_ok

theorem logTwoOverLogNat4_arith_sound :
    LogTwoOverLogNatArithCert.Sound logTwoOverLogNatArithCert4 :=
  logTwoOverLogNatArith_sound logTwoOverLogNatArithCert4
    logTwoOverLogNatArithCert4_ok

end BEDC.Real.RatLogEnclosure
