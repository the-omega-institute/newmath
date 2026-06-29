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

structure AtanhTailCert where
  z : Q
  M : Nat
  K : Nat

namespace AtanhTailCert

def check (c : AtanhTailCert) : Bool :=
  qLeBool 0 c.z &&
    (qLtBool c.z 1 &&
      qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M))

def Sound (c : AtanhTailCert) : Prop :=
  (0 : Q) <= c.z ∧
    c.z < 1 ∧
      atanhFiniteTail c.z c.M c.K <= atanhTail c.z c.M

end AtanhTailCert

theorem atanhFiniteTail_cert_bound {z : Q} {M K : Nat}
    (hfinite : qLeBool (atanhFiniteTail z M K) (atanhTail z M) = true) :
    atanhFiniteTail z M K <= atanhTail z M := by
  exact qLe_of_qLeBool hfinite

theorem atanhTailCert_sound (c : AtanhTailCert) :
    AtanhTailCert.check c = true -> AtanhTailCert.Sound c := by
  intro h
  unfold AtanhTailCert.check at h
  have h_nonneg_bool :
      qLeBool 0 c.z = true :=
    boolAndLeftTrue h
  have h_rest :
      (qLtBool c.z 1 &&
        qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M)) = true :=
    boolAndRightTrue h
  have h_lt_bool :
      qLtBool c.z 1 = true :=
    boolAndLeftTrue h_rest
  have h_tail_bool :
      qLeBool (atanhFiniteTail c.z c.M c.K) (atanhTail c.z c.M) = true :=
    boolAndRightTrue h_rest
  exact
    And.intro (qLe_of_qLeBool h_nonneg_bool)
      (And.intro (qLt_of_qLtBool h_lt_bool)
        (atanhFiniteTail_cert_bound h_tail_bool))

def sampleAtanhTailCert : AtanhTailCert :=
  { z := 1 / 3, M := 2, K := 3 }

theorem sampleAtanhTailCert_ok :
    AtanhTailCert.check sampleAtanhTailCert = true := by
  rfl

theorem sampleAtanhTailCert_sound :
    AtanhTailCert.Sound sampleAtanhTailCert :=
  atanhTailCert_sound sampleAtanhTailCert sampleAtanhTailCert_ok

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

structure LogNatFormulaCert where
  n : Nat
  M : Nat
  K : Nat

namespace LogNatFormulaCert

def lnTwoTailCert (c : LogNatFormulaCert) : AtanhTailCert :=
  { z := 1 / 3, M := c.M, K := c.K }

def zTailCert (c : LogNatFormulaCert) : AtanhTailCert :=
  { z := zLogSmall c.n, M := c.M, K := c.K }

def check (c : LogNatFormulaCert) : Bool :=
    qLeBool 1 ((c.n : Nat) : Q) &&
    (qLeBool ((c.n : Nat) : Q) ((logEnclosureLimit : Nat) : Q) &&
      (AtanhTailCert.check (lnTwoTailCert c) &&
        (AtanhTailCert.check (zTailCert c) &&
          qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M))))

def Sound (c : LogNatFormulaCert) : Prop :=
  (1 : Q) <= ((c.n : Nat) : Q) ∧
    ((c.n : Nat) : Q) <= ((logEnclosureLimit : Nat) : Q) ∧
      AtanhTailCert.Sound (lnTwoTailCert c) ∧
        AtanhTailCert.Sound (zTailCert c) ∧
          logLoSmall c.n c.M <= logHiSmall c.n c.M

end LogNatFormulaCert

theorem logFormulaCert_sound (c : LogNatFormulaCert) :
    LogNatFormulaCert.check c = true -> LogNatFormulaCert.Sound c := by
  intro h
  unfold LogNatFormulaCert.check at h
  have h_n_lower :
      qLeBool 1 ((c.n : Nat) : Q) = true :=
    boolAndLeftTrue h
  have h_after_lower :
      (qLeBool ((c.n : Nat) : Q) ((logEnclosureLimit : Nat) : Q) &&
        (AtanhTailCert.check (LogNatFormulaCert.lnTwoTailCert c) &&
          (AtanhTailCert.check (LogNatFormulaCert.zTailCert c) &&
            qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M)))) = true :=
    boolAndRightTrue h
  have h_n_upper :
      qLeBool ((c.n : Nat) : Q) ((logEnclosureLimit : Nat) : Q) = true :=
    boolAndLeftTrue h_after_lower
  have h_after_upper :
      (AtanhTailCert.check (LogNatFormulaCert.lnTwoTailCert c) &&
        (AtanhTailCert.check (LogNatFormulaCert.zTailCert c) &&
          qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M))) = true :=
    boolAndRightTrue h_after_lower
  have h_ln2 :
      AtanhTailCert.check (LogNatFormulaCert.lnTwoTailCert c) = true :=
    boolAndLeftTrue h_after_upper
  have h_after_ln2 :
      (AtanhTailCert.check (LogNatFormulaCert.zTailCert c) &&
        qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M)) = true :=
    boolAndRightTrue h_after_upper
  have h_z :
      AtanhTailCert.check (LogNatFormulaCert.zTailCert c) = true :=
    boolAndLeftTrue h_after_ln2
  have h_ordered :
      qLeBool (logLoSmall c.n c.M) (logHiSmall c.n c.M) = true :=
    boolAndRightTrue h_after_ln2
  exact
    And.intro (qLe_of_qLeBool h_n_lower)
      (And.intro (qLe_of_qLeBool h_n_upper)
          (And.intro
          (atanhTailCert_sound (LogNatFormulaCert.lnTwoTailCert c) h_ln2)
          (And.intro
            (atanhTailCert_sound (LogNatFormulaCert.zTailCert c) h_z)
            (qLe_of_qLeBool h_ordered))))

def logNatCert1 : LogNatFormulaCert :=
  { n := 1, M := logExampleM, K := logExampleTailK }

def logNatCert2 : LogNatFormulaCert :=
  { n := 2, M := logExampleM, K := logExampleTailK }

def logNatCert3 : LogNatFormulaCert :=
  { n := 3, M := logExampleM, K := logExampleTailK }

def logNatCert4 : LogNatFormulaCert :=
  { n := 4, M := logExampleM, K := logExampleTailK }

def logNatCert5 : LogNatFormulaCert :=
  { n := 5, M := logExampleM, K := logExampleTailK }

def logNatCert6 : LogNatFormulaCert :=
  { n := 6, M := logExampleM, K := logExampleTailK }

def logNatCert7 : LogNatFormulaCert :=
  { n := 7, M := logExampleM, K := logExampleTailK }

def logNatCert8 : LogNatFormulaCert :=
  { n := 8, M := logExampleM, K := logExampleTailK }

theorem logNatCert1_ok :
    LogNatFormulaCert.check logNatCert1 = true := by
  rfl

theorem logNatCert2_ok :
    LogNatFormulaCert.check logNatCert2 = true := by
  rfl

theorem logNatCert3_ok :
    LogNatFormulaCert.check logNatCert3 = true := by
  rfl

theorem logNatCert4_ok :
    LogNatFormulaCert.check logNatCert4 = true := by
  rfl

theorem logNatCert5_ok :
    LogNatFormulaCert.check logNatCert5 = true := by
  rfl

theorem logNatCert6_ok :
    LogNatFormulaCert.check logNatCert6 = true := by
  rfl

theorem logNatCert7_ok :
    LogNatFormulaCert.check logNatCert7 = true := by
  rfl

theorem logNatCert8_ok :
    LogNatFormulaCert.check logNatCert8 = true := by
  rfl

theorem logNat1_formula_sound :
    LogNatFormulaCert.Sound logNatCert1 :=
  logFormulaCert_sound logNatCert1 logNatCert1_ok

theorem logNat2_formula_sound :
    LogNatFormulaCert.Sound logNatCert2 :=
  logFormulaCert_sound logNatCert2 logNatCert2_ok

theorem logNat3_formula_sound :
    LogNatFormulaCert.Sound logNatCert3 :=
  logFormulaCert_sound logNatCert3 logNatCert3_ok

theorem logNat4_formula_sound :
    LogNatFormulaCert.Sound logNatCert4 :=
  logFormulaCert_sound logNatCert4 logNatCert4_ok

theorem logNat5_formula_sound :
    LogNatFormulaCert.Sound logNatCert5 :=
  logFormulaCert_sound logNatCert5 logNatCert5_ok

theorem logNat6_formula_sound :
    LogNatFormulaCert.Sound logNatCert6 :=
  logFormulaCert_sound logNatCert6 logNatCert6_ok

theorem logNat7_formula_sound :
    LogNatFormulaCert.Sound logNatCert7 :=
  logFormulaCert_sound logNatCert7 logNatCert7_ok

theorem logNat8_formula_sound :
    LogNatFormulaCert.Sound logNatCert8 :=
  logFormulaCert_sound logNatCert8 logNatCert8_ok

structure LogTwoOverLogNatFormulaCert where
  target : LogNatFormulaCert

namespace LogTwoOverLogNatFormulaCert

def numerator : LogNatFormulaCert :=
  logNatCert2

def lo (c : LogTwoOverLogNatFormulaCert) : Q :=
  logLoSmall 2 c.target.M / logHiSmall c.target.n c.target.M

def hi (c : LogTwoOverLogNatFormulaCert) : Q :=
  logHiSmall 2 c.target.M / logLoSmall c.target.n c.target.M

def check (c : LogTwoOverLogNatFormulaCert) : Bool :=
  LogNatFormulaCert.check numerator &&
    (LogNatFormulaCert.check c.target &&
      (qLtBool 0 (logLoSmall c.target.n c.target.M) &&
        qLeBool (lo c) (hi c)))

def Sound (c : LogTwoOverLogNatFormulaCert) : Prop :=
  LogNatFormulaCert.Sound numerator ∧
    LogNatFormulaCert.Sound c.target ∧
      (0 : Q) < logLoSmall c.target.n c.target.M ∧
        lo c <= hi c

end LogTwoOverLogNatFormulaCert

theorem logTwoOverLogNatFormula_sound (c : LogTwoOverLogNatFormulaCert) :
    LogTwoOverLogNatFormulaCert.check c = true -> LogTwoOverLogNatFormulaCert.Sound c := by
  intro h
  unfold LogTwoOverLogNatFormulaCert.check at h
  have h_numerator :
      LogNatFormulaCert.check LogTwoOverLogNatFormulaCert.numerator = true :=
    boolAndLeftTrue h
  have h_after_numerator :
      (LogNatFormulaCert.check c.target &&
        (qLtBool 0 (logLoSmall c.target.n c.target.M) &&
          qLeBool (LogTwoOverLogNatFormulaCert.lo c) (LogTwoOverLogNatFormulaCert.hi c))) = true :=
    boolAndRightTrue h
  have h_target :
      LogNatFormulaCert.check c.target = true :=
    boolAndLeftTrue h_after_numerator
  have h_after_target :
      (qLtBool 0 (logLoSmall c.target.n c.target.M) &&
        qLeBool (LogTwoOverLogNatFormulaCert.lo c) (LogTwoOverLogNatFormulaCert.hi c)) = true :=
    boolAndRightTrue h_after_numerator
  have h_positive :
      qLtBool 0 (logLoSmall c.target.n c.target.M) = true :=
    boolAndLeftTrue h_after_target
  have h_ordered :
      qLeBool (LogTwoOverLogNatFormulaCert.lo c) (LogTwoOverLogNatFormulaCert.hi c) = true :=
    boolAndRightTrue h_after_target
  exact
    And.intro (logFormulaCert_sound LogTwoOverLogNatFormulaCert.numerator h_numerator)
      (And.intro (logFormulaCert_sound c.target h_target)
        (And.intro (qLt_of_qLtBool h_positive)
          (qLe_of_qLeBool h_ordered)))

def logTwoOverLogNatFormulaCert2 : LogTwoOverLogNatFormulaCert :=
  { target := logNatCert2 }

def logTwoOverLogNatFormulaCert3 : LogTwoOverLogNatFormulaCert :=
  { target := logNatCert3 }

def logTwoOverLogNatFormulaCert4 : LogTwoOverLogNatFormulaCert :=
  { target := logNatCert4 }

theorem logTwoOverLogNatFormulaCert2_ok :
    LogTwoOverLogNatFormulaCert.check logTwoOverLogNatFormulaCert2 = true := by
  rfl

theorem logTwoOverLogNatFormulaCert3_ok :
    LogTwoOverLogNatFormulaCert.check logTwoOverLogNatFormulaCert3 = true := by
  rfl

theorem logTwoOverLogNatFormulaCert4_ok :
    LogTwoOverLogNatFormulaCert.check logTwoOverLogNatFormulaCert4 = true := by
  rfl

theorem logTwoOverLogNat2_formula_sound :
    LogTwoOverLogNatFormulaCert.Sound logTwoOverLogNatFormulaCert2 :=
  logTwoOverLogNatFormula_sound logTwoOverLogNatFormulaCert2 logTwoOverLogNatFormulaCert2_ok

theorem logTwoOverLogNat3_formula_sound :
    LogTwoOverLogNatFormulaCert.Sound logTwoOverLogNatFormulaCert3 :=
  logTwoOverLogNatFormula_sound logTwoOverLogNatFormulaCert3 logTwoOverLogNatFormulaCert3_ok

theorem logTwoOverLogNat4_formula_sound :
    LogTwoOverLogNatFormulaCert.Sound logTwoOverLogNatFormulaCert4 :=
  logTwoOverLogNatFormula_sound logTwoOverLogNatFormulaCert4 logTwoOverLogNatFormulaCert4_ok

end BEDC.Real.RatLogEnclosure
