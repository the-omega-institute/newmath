namespace BEDC.Derived.LucasCubeDisjointPairSilver

/-!
Lucas cube Lambda_m disjoint ordered-pair counts are represented by
`D_m = tr(M^m)` for
`M = [[1,1,1],[1,0,1],[1,1,0]]`.
The characteristic polynomial is `(x+1)(x^2-2x-1)`, so the spectrum
contains the silver/Pell constants `1 + sqrt 2` and `1 - sqrt 2`.
This finite transfer certificate connects golden-mean/Fibonacci cyclic
word counting to the Pell/silver metallic constant and closes the
fib_reality claim `lucas-cube.disjoint-pair-trace`.
-/

structure Mat3 where
  aa : Nat
  ab : Nat
  ac : Nat
  ba : Nat
  bb : Nat
  bc : Nat
  ca : Nat
  cb : Nat
  cc : Nat
deriving DecidableEq

structure State3 where
  top : Nat
  middle : Nat
  bottom : Nat
deriving DecidableEq

def I3 : Mat3 :=
  ⟨1, 0, 0,
    0, 1, 0,
    0, 0, 1⟩

def transferM : Mat3 :=
  ⟨1, 1, 1,
    1, 0, 1,
    1, 1, 0⟩

def matAdd (X Y : Mat3) : Mat3 :=
  ⟨X.aa + Y.aa, X.ab + Y.ab, X.ac + Y.ac,
    X.ba + Y.ba, X.bb + Y.bb, X.bc + Y.bc,
    X.ca + Y.ca, X.cb + Y.cb, X.cc + Y.cc⟩

def scale3 (k : Nat) (X : Mat3) : Mat3 :=
  ⟨k * X.aa, k * X.ab, k * X.ac,
    k * X.ba, k * X.bb, k * X.bc,
    k * X.ca, k * X.cb, k * X.cc⟩

def mmul3 (X Y : Mat3) : Mat3 :=
  ⟨X.aa * Y.aa + X.ab * Y.ba + X.ac * Y.ca,
    X.aa * Y.ab + X.ab * Y.bb + X.ac * Y.cb,
    X.aa * Y.ac + X.ab * Y.bc + X.ac * Y.cc,
    X.ba * Y.aa + X.bb * Y.ba + X.bc * Y.ca,
    X.ba * Y.ab + X.bb * Y.bb + X.bc * Y.cb,
    X.ba * Y.ac + X.bb * Y.bc + X.bc * Y.cc,
    X.ca * Y.aa + X.cb * Y.ba + X.cc * Y.ca,
    X.ca * Y.ab + X.cb * Y.bb + X.cc * Y.cb,
    X.ca * Y.ac + X.cb * Y.bc + X.cc * Y.cc⟩

def mpow3 : Nat -> Mat3
  | 0 => I3
  | m + 1 => mmul3 (mpow3 m) transferM

def trace3 (X : Mat3) : Nat :=
  X.aa + X.bb + X.cc

def disjPairCount (m : Nat) : Nat :=
  trace3 (mpow3 m)

def matVec (X : Mat3) (v : State3) : State3 :=
  ⟨X.aa * v.top + X.ab * v.middle + X.ac * v.bottom,
    X.ba * v.top + X.bb * v.middle + X.bc * v.bottom,
    X.ca * v.top + X.cb * v.middle + X.cc * v.bottom⟩

theorem disjpair_1 :
    disjPairCount 1 = 1 := by
  rfl

theorem disjpair_2 :
    disjPairCount 2 = 7 := by
  rfl

theorem disjpair_3 :
    disjPairCount 3 = 13 := by
  rfl

theorem disjpair_4 :
    disjPairCount 4 = 35 := by
  rfl

theorem disjpair_5 :
    disjPairCount 5 = 81 := by
  rfl

theorem disjpair_6 :
    disjPairCount 6 = 199 := by
  rfl

theorem disjpair_7 :
    disjPairCount 7 = 477 := by
  rfl

theorem disjpair_8 :
    disjPairCount 8 = 1155 := by
  rfl

theorem disjpair_9 :
    disjPairCount 9 = 2785 := by
  rfl

theorem disjpair_10 :
    disjPairCount 10 = 6727 := by
  rfl

theorem transferM_cayley_hamilton :
    mmul3 (mmul3 transferM transferM) transferM =
      matAdd (matAdd (mmul3 transferM transferM) (scale3 3 transferM)) I3 := by
  rfl

theorem disjpair_recurrence_0 :
    disjPairCount (0 + 3) =
      disjPairCount (0 + 2) + 3 * disjPairCount (0 + 1) + disjPairCount 0 := by
  rfl

theorem disjpair_recurrence_1 :
    disjPairCount (1 + 3) =
      disjPairCount (1 + 2) + 3 * disjPairCount (1 + 1) + disjPairCount 1 := by
  rfl

theorem disjpair_recurrence_2 :
    disjPairCount (2 + 3) =
      disjPairCount (2 + 2) + 3 * disjPairCount (2 + 1) + disjPairCount 2 := by
  rfl

theorem disjpair_recurrence_3 :
    disjPairCount (3 + 3) =
      disjPairCount (3 + 2) + 3 * disjPairCount (3 + 1) + disjPairCount 3 := by
  rfl

theorem disjpair_recurrence_4 :
    disjPairCount (4 + 3) =
      disjPairCount (4 + 2) + 3 * disjPairCount (4 + 1) + disjPairCount 4 := by
  rfl

theorem disjpair_recurrence_5 :
    disjPairCount (5 + 3) =
      disjPairCount (5 + 2) + 3 * disjPairCount (5 + 1) + disjPairCount 5 := by
  rfl

theorem disjpair_recurrence_6 :
    disjPairCount (6 + 3) =
      disjPairCount (6 + 2) + 3 * disjPairCount (6 + 1) + disjPairCount 6 := by
  rfl

theorem disjpair_recurrence_7 :
    disjPairCount (7 + 3) =
      disjPairCount (7 + 2) + 3 * disjPairCount (7 + 1) + disjPairCount 7 := by
  rfl

theorem lucas_cube_disjoint_pair_silver_certificate :
    disjPairCount 1 = 1 ∧
    disjPairCount 2 = 7 ∧
    disjPairCount 3 = 13 ∧
    disjPairCount 4 = 35 ∧
    disjPairCount 5 = 81 ∧
    disjPairCount 6 = 199 ∧
    disjPairCount 7 = 477 ∧
    disjPairCount 8 = 1155 ∧
    disjPairCount 9 = 2785 ∧
    disjPairCount 10 = 6727 ∧
    disjPairCount (0 + 3) =
      disjPairCount (0 + 2) + 3 * disjPairCount (0 + 1) + disjPairCount 0 ∧
    disjPairCount (1 + 3) =
      disjPairCount (1 + 2) + 3 * disjPairCount (1 + 1) + disjPairCount 1 ∧
    disjPairCount (2 + 3) =
      disjPairCount (2 + 2) + 3 * disjPairCount (2 + 1) + disjPairCount 2 ∧
    disjPairCount (3 + 3) =
      disjPairCount (3 + 2) + 3 * disjPairCount (3 + 1) + disjPairCount 3 ∧
    disjPairCount (4 + 3) =
      disjPairCount (4 + 2) + 3 * disjPairCount (4 + 1) + disjPairCount 4 ∧
    disjPairCount (5 + 3) =
      disjPairCount (5 + 2) + 3 * disjPairCount (5 + 1) + disjPairCount 5 ∧
    disjPairCount (6 + 3) =
      disjPairCount (6 + 2) + 3 * disjPairCount (6 + 1) + disjPairCount 6 ∧
    disjPairCount (7 + 3) =
      disjPairCount (7 + 2) + 3 * disjPairCount (7 + 1) + disjPairCount 7 ∧
    mmul3 (mmul3 transferM transferM) transferM =
      matAdd (matAdd (mmul3 transferM transferM) (scale3 3 transferM)) I3 := by
  constructor
  · exact disjpair_1
  constructor
  · exact disjpair_2
  constructor
  · exact disjpair_3
  constructor
  · exact disjpair_4
  constructor
  · exact disjpair_5
  constructor
  · exact disjpair_6
  constructor
  · exact disjpair_7
  constructor
  · exact disjpair_8
  constructor
  · exact disjpair_9
  constructor
  · exact disjpair_10
  constructor
  · exact disjpair_recurrence_0
  constructor
  · exact disjpair_recurrence_1
  constructor
  · exact disjpair_recurrence_2
  constructor
  · exact disjpair_recurrence_3
  constructor
  · exact disjpair_recurrence_4
  constructor
  · exact disjpair_recurrence_5
  constructor
  · exact disjpair_recurrence_6
  constructor
  · exact disjpair_recurrence_7
  · exact transferM_cayley_hamilton

end BEDC.Derived.LucasCubeDisjointPairSilver
