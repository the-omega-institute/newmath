namespace BEDC.Derived.Window6EdgeCokernelClock

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Vec4 := Int × Int × Int × Int

structure Mat4 where
  r0 : Vec4
  r1 : Vec4
  r2 : Vec4
  r3 : Vec4
deriving DecidableEq, Repr

def mod10 (x : Int) : Int :=
  x % 10

def edgeMatrix : Mat4 :=
  { r0 := (28, 63, 23, 20)
    r1 := (63, 21, 21, 6)
    r2 := (23, 21, 2, 6)
    r3 := (20, 6, 6, 2) }

def get (v : Vec4) : Nat → Int
  | 0 => v.1
  | 1 => v.2.1
  | 2 => v.2.2.1
  | _ => v.2.2.2

def row (E : Mat4) : Nat → Vec4
  | 0 => E.r0
  | 1 => E.r1
  | 2 => E.r2
  | _ => E.r3

def entry (E : Mat4) (i j : Nat) : Int :=
  get (row E i) j

def dot (a b : Vec4) : Int :=
  get a 0 * get b 0 + get a 1 * get b 1 + get a 2 * get b 2 + get a 3 * get b 3

def col (E : Mat4) (j : Nat) : Vec4 :=
  (entry E 0 j, entry E 1 j, entry E 2 j, entry E 3 j)

def rowMul (v : Vec4) (E : Mat4) : Vec4 :=
  (mod10 (dot v (col E 0)),
   mod10 (dot v (col E 1)),
   mod10 (dot v (col E 2)),
   mod10 (dot v (col E 3)))

def matVec (E : Mat4) (v : Vec4) : Vec4 :=
  (mod10 (dot (row E 0) v),
   mod10 (dot (row E 1) v),
   mod10 (dot (row E 2) v),
   mod10 (dot (row E 3) v))

def det3
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : Int :=
  a00 * (a11 * a22 - a12 * a21)
    - a01 * (a10 * a22 - a12 * a20)
    + a02 * (a10 * a21 - a11 * a20)

def minorRow0 (E : Mat4) : Nat → Int
  | 0 =>
      det3
        (entry E 1 1) (entry E 1 2) (entry E 1 3)
        (entry E 2 1) (entry E 2 2) (entry E 2 3)
        (entry E 3 1) (entry E 3 2) (entry E 3 3)
  | 1 =>
      det3
        (entry E 1 0) (entry E 1 2) (entry E 1 3)
        (entry E 2 0) (entry E 2 2) (entry E 2 3)
        (entry E 3 0) (entry E 3 2) (entry E 3 3)
  | 2 =>
      det3
        (entry E 1 0) (entry E 1 1) (entry E 1 3)
        (entry E 2 0) (entry E 2 1) (entry E 2 3)
        (entry E 3 0) (entry E 3 1) (entry E 3 3)
  | _ =>
      det3
        (entry E 1 0) (entry E 1 1) (entry E 1 2)
        (entry E 2 0) (entry E 2 1) (entry E 2 2)
        (entry E 3 0) (entry E 3 1) (entry E 3 2)

def det4 (E : Mat4) : Int :=
  entry E 0 0 * minorRow0 E 0
    - entry E 0 1 * minorRow0 E 1
    + entry E 0 2 * minorRow0 E 2
    - entry E 0 3 * minorRow0 E 3

def chi : Vec4 :=
  (2, 8, 0, 1)

def allVec4Mod10 : List Vec4 :=
  (List.range 10).foldl
    (fun acc a =>
      acc ++ (List.range 10).foldl
        (fun acc b =>
          acc ++ (List.range 10).foldl
            (fun acc c =>
              acc ++ (List.range 10).map
                (fun d => (Int.ofNat a, Int.ofNat b, Int.ofNat c, Int.ofNat d)))
            [])
        [])
    []

def leftKernelMod10 : List Vec4 :=
  allVec4Mod10.filter (fun v => rowMul v edgeMatrix == (0, 0, 0, 0))

def chiOrbitContains (v : Vec4) : Bool :=
  (List.range 10).any
    (fun t =>
      v ==
        (mod10 (Int.ofNat t * get chi 0),
         mod10 (Int.ofNat t * get chi 1),
         mod10 (Int.ofNat t * get chi 2),
         mod10 (Int.ofNat t * get chi 3)))

def cyclicChiMod10 : List Vec4 :=
  allVec4Mod10.filter chiOrbitContains

def pinnedChiKernel : List Vec4 :=
  leftKernelMod10.filter (fun v => get v 3 == 1)

def chiEZeroCheck : Bool :=
  rowMul chi edgeMatrix == (0, 0, 0, 0)

def cellResidues : Vec4 :=
  (get chi 0, get chi 1, get chi 2, get chi 3)

def seamGrade : Int :=
  mod10 (get chi 1 - get chi 3)

def witnessRows : List (Vec4 × Vec4) :=
  [((1, 1, 0, 1), (1, 0, 0, 8)),
   ((1, 5, 9, 4), (0, 1, 0, 2)),
   ((0, 9, 1, 0), (0, 0, 1, 0))]

def witnessIdentitiesCheck : Bool :=
  witnessRows.all (fun row => matVec edgeMatrix row.fst == row.snd)

def gcdKernelCheck : Bool :=
  Nat.gcd 10 3 == 1 && Nat.gcd 10 3450 == 10

def phaseLockAInt : Int :=
  mod10 (seamGrade - 7)

theorem edge_matrix_det :
    det4 edgeMatrix = 10350 := by
  decide

theorem edge_cokernel_clock_gcd_core :
    gcdKernelCheck = true := by
  decide

theorem left_kernel_mod10_is_cyclic10 :
    leftKernelMod10 = cyclicChiMod10 ∧ leftKernelMod10.length = 10 ∧ pinnedChiKernel = [chi] := by
  decide

theorem chi_E_zero_mod10 :
    chiEZeroCheck = true := by
  decide

theorem cell_residues :
    cellResidues = (2, 8, 0, 1) := by
  decide

theorem seam_grade_seven :
    seamGrade = 7 := by
  decide

theorem witness_identities :
    witnessIdentitiesCheck = true := by
  decide

theorem phase_lock_a_int_zero :
    phaseLockAInt = 0 := by
  decide

end BEDC.Derived.Window6EdgeCokernelClock
