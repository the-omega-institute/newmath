import BEDC.Derived.RHRoute.OCLSDRegisterWeight
import BEDC.Derived.RHRoute.FiniteEulerDirichlet
import BEDC.Derived.FibonacciUp
import BEDC.Derived.ZeckendorfUp

/-
S3 Layer 1 — OCLSD register → finite Euler–Dirichlet bridge (pointwise Nat kernel).

After S1 (Weyl gate) disproved "OCLSD spectrum = zeta zeros" for the BC-locked log-n generator,
S3 supplies the correct Bost–Connes side: the OCLSD prime–Fibonacci register maps *canonically*
onto Loning's encoded-Dirichlet interface, so the existing finite Euler–Dirichlet theorem
(`FiniteEulerDirichlet.finiteEuler_eq_encodedDirichlet`) can be consumed by OCLSD WITHOUT
changing the register semantics.

This module is only the pointwise Nat bridge `encodedNat R = encNat (pzgToExponents R)` under the
index map `(p,k) ↦ (p, fib k)`.  It does NOT reprove Euler = Dirichlet — that theorem, the
encoded-Dirichlet term machinery and the unique-factorization core all belong to Loning's
`FiniteEulerDirichlet` / `PrimeUp` lanes and are consumed here, not re-derived.  0-axiom /
propext-free.
-/

namespace BEDC.Derived.RHRoute.OCLSDRegisterDirichletBridge

open BEDC.Derived.RHRoute.OCLSDRegisterWeight
open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra
open BEDC.Derived.RHRoute.FiniteEulerDirichlet
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp (natToUnary natToUnary_length)
open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)

/-- Propext-free `a*b*c = a*(b*c)` (core `Nat.mul_assoc` depends on propext). -/
private theorem natMul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, ih]

/-- Propext-free `0 * a = 0`. -/
private theorem natZero_mul (a : Nat) : 0 * a = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Nat.mul_succ, ih]

/-- Propext-free `a*b = b*a` (core `Nat.mul_comm` depends on propext). -/
private theorem natMul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => rw [Nat.mul_zero, natZero_mul]
  | succ b ih => rw [Nat.mul_succ, Nat.succ_mul, ih]

/-- `primeFlatProductNat` (∏ of `bwordLength`) is multiplicative over list append. -/
private theorem primeFlatProductNat_append :
    ∀ (xs ys : List BHist),
      primeFlatProductNat (xs ++ ys)
        = primeFlatProductNat xs * primeFlatProductNat ys
  | [], ys => (Nat.one_mul (primeFlatProductNat ys)).symm
  | x :: xs, ys => by
      show bwordLength x * primeFlatProductNat (xs ++ ys)
        = bwordLength x * primeFlatProductNat xs * primeFlatProductNat ys
      rw [primeFlatProductNat_append xs ys, natMul_assoc]

/-- `primeFlatProductNat (replicate e q) = (bwordLength q) ^ e`. -/
private theorem primeFlatProductNat_replicate (q : BHist) :
    ∀ e : Nat, primeFlatProductNat (List.replicate e q) = (bwordLength q) ^ e
  | 0 => rfl
  | Nat.succ e => by
      show bwordLength q * primeFlatProductNat (List.replicate e q)
        = (bwordLength q) ^ (Nat.succ e)
      rw [primeFlatProductNat_replicate q e, Nat.pow_succ, natMul_comm]

/-- `encNat [] = 1`. -/
theorem encNat_nil : encNat ([] : List (Nat × Nat)) = 1 := rfl

/-- **Consing one prime-exponent atom multiplies in `p^e`.** -/
theorem encNat_cons (p e : Nat) (xs : List (Nat × Nat)) :
    encNat ((p, e) :: xs) = p ^ e * encNat xs := by
  show primeFlatProductNat (List.replicate e (natToUnary p) ++ exponentSpine xs)
    = p ^ e * primeFlatProductNat (exponentSpine xs)
  rw [primeFlatProductNat_append, primeFlatProductNat_replicate, natToUnary_length]

/-- Register → Loning exponent vector under `(p,k) ↦ (p, fib k)`. -/
def pzgToExponents : PZGRow → List (Nat × Nat)
  | PZGRow.nil => []
  | PZGRow.cons p k rest => (p, fib k) :: pzgToExponents rest

/-- **S3 Layer-1 load-bearing bridge**: the OCLSD register's encoded integer is exactly Loning's
`encNat` of the Fibonacci-mapped exponent vector.  Pure `Nat`, no prime uniqueness needed — this
is the adapter kernel that lets OCLSD consume the finite Euler–Dirichlet machinery. -/
theorem encodedNat_eq_encNat_fibmap :
    ∀ R : PZGRow, encodedNat R = encNat (pzgToExponents R)
  | PZGRow.nil => rfl
  | PZGRow.cons p k rest => by
      show p ^ (fib k) * encodedNat rest
        = encNat ((p, fib k) :: pzgToExponents rest)
      rw [encNat_cons, encodedNat_eq_encNat_fibmap rest]

/-! ## Layer 2 — canonical Zeckendorf register realizes `p^e` (uses Loning's `zeckendorf_sum_restore`). -/

/-- The OCLSD register's Fibonacci equals the shared `FibonacciUp.fib` (same standard Fibonacci;
only the addition order in the recurrence differs). -/
private theorem fib_eq_pair : ∀ n : Nat,
    fib n = BEDC.Derived.FibonacciUp.fib n
      ∧ fib (n + 1) = BEDC.Derived.FibonacciUp.fib (n + 1)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
      obtain ⟨h0, h1⟩ := fib_eq_pair n
      refine ⟨h1, ?_⟩
      show fib n + fib (n + 1)
        = BEDC.Derived.FibonacciUp.fib (n + 1) + BEDC.Derived.FibonacciUp.fib n
      rw [h0, h1, Nat.add_comm]

theorem fib_eq (n : Nat) : fib n = BEDC.Derived.FibonacciUp.fib n := (fib_eq_pair n).1

/-- Propext-free `a^(m+n) = a^m * a^n`. -/
private theorem natPow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, natMul_assoc]

/-- Register built from a prime's Zeckendorf index list: `index ↦ (p, index+2)`. -/
def pzgFromIndices (p : Nat) : List Nat → PZGRow
  | [] => PZGRow.nil
  | index :: rest => PZGRow.cons p (index + 2) (pzgFromIndices p rest)

/-- Sum of `fib (index+2)` over a Zeckendorf index list. -/
def sumMyFib : List Nat → Nat
  | [] => 0
  | index :: rest => fib (index + 2) + sumMyFib rest

theorem sumMyFib_eq_zeckendorfValue (indices : List Nat) :
    sumMyFib indices = BEDC.Derived.ZeckendorfUp.zeckendorfValue indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      show fib (index + 2) + sumMyFib rest
        = BEDC.Derived.ZeckendorfUp.fibonacciTerm index
          + BEDC.Derived.ZeckendorfUp.zeckendorfValue rest
      unfold BEDC.Derived.ZeckendorfUp.fibonacciTerm
      rw [ih, fib_eq (index + 2)]

theorem encodedNat_pzgFromIndices (p : Nat) (indices : List Nat) :
    encodedNat (pzgFromIndices p indices) = p ^ (sumMyFib indices) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      show p ^ (fib (index + 2)) * encodedNat (pzgFromIndices p rest)
        = p ^ (fib (index + 2) + sumMyFib rest)
      rw [ih, natPow_add]

/-- Canonical Zeckendorf register realizing exponent `e` on prime `p` (NOT a raw multiset). -/
def pzgOfExponent (p e : Nat) : PZGRow :=
  pzgFromIndices p (BEDC.Derived.ZeckendorfUp.zeckendorf e)

/-- **S3 Layer-2 core**: the canonical Zeckendorf register on prime `p` encodes exactly `p^e`,
because `Σ fib(index+2) = e` (Loning's `zeckendorf_sum_restore`, consumed not re-derived).  This
is the genuine Zeckendorf increment: OCLSD's Fibonacci register realizes an arbitrary prime power
canonically. -/
theorem encodedNat_pzgOfExponent (p e : Nat) :
    encodedNat (pzgOfExponent p e) = p ^ e := by
  show encodedNat (pzgFromIndices p (BEDC.Derived.ZeckendorfUp.zeckendorf e)) = p ^ e
  rw [encodedNat_pzgFromIndices, sumMyFib_eq_zeckendorfValue,
    BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore]

/-- Multi-prime canonical register from an exponent vector `[(p,e),…]`. -/
def pzgOfExponentVector : List (Nat × Nat) → PZGRow
  | [] => PZGRow.nil
  | (p, e) :: rest => pzgAppend (pzgOfExponent p e) (pzgOfExponentVector rest)

/-- **S3 Layer-2 (multi-prime)**: the canonical Zeckendorf register of an exponent vector encodes
exactly Loning's `encNat` of it.  Combines the per-prime Zeckendorf realization
(`encodedNat_pzgOfExponent`) with the register-concatenation homomorphism (`encodedNat_append`, O3)
and `encNat_cons`.  This is the register side of the finite Euler–Dirichlet correspondence, ready
to feed Loning's `finiteEuler_eq_encodedDirichlet` at the window level. -/
theorem encodedNat_pzgOfExponentVector (xs : List (Nat × Nat)) :
    encodedNat (pzgOfExponentVector xs) = encNat xs := by
  induction xs with
  | nil => rfl
  | cons pe rest ih =>
      obtain ⟨p, e⟩ := pe
      show encodedNat (pzgAppend (pzgOfExponent p e) (pzgOfExponentVector rest))
        = encNat ((p, e) :: rest)
      rw [encodedNat_append, encodedNat_pzgOfExponent, ih, encNat_cons]

/-! ## Layer 3 — window-level partition: OCLSD register finite Euler–Dirichlet enumeration.

Layers 1–2 aligned the *single-integer* encoding (`encodedNat R = encNat …`).  Layer 3 lifts that
to the **finite-window enumeration**: it builds the OCLSD register list that realizes every term of
a finite Euler product window, and proves its integer image equals the integer image of Loning's
`encodedDirichletTerms` — then, consuming Loning's `finiteEuler_eq_encodedDirichlet`, equals the
integer image of the finite Euler-product expansion `eulerExpandTerms`.  This is the headline of the
user's S3: *the OCLSD register finite-window partition = the finite-window Euler product, as a
kernel-checked theorem*.

Honest scope: the finite Euler = Dirichlet identity itself is Loning's theorem (consumed, not
re-derived); the genuine OCLSD increment here is the register-side enumeration
(`pzgEncodedDirichlet`, the Fibonacci/Zeckendorf register realizing each Euler term) and its
integer alignment.  Terms are read as integers through the factor spine `termValueF` (avoiding the
`BHist` `encoded`/`hsame` layer).  0-axiom / propext-free.  The `SpectralZeroIdentity` Hilbert–Pólya
wall is untouched — this is the Bost–Connes partition-function side, which S1 left standing after it
disproved the spectral (zero-set) side.
-/

/-- Propext-free `List.map` over append (core `List.map_append` route can leak `propext`). -/
private theorem list_map_append {α β : Type _} (f : α → β) :
    ∀ xs ys : List α, (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: xs, ys => congrArg (List.cons (f x)) (list_map_append f xs ys)

/-- A Loning Dirichlet term read as its integer value through the factor spine. -/
def termValueF (t : FormalEulerTerm) : Nat := primeFlatProductNat t.factors

/-- Attaching `formalTermFromFactors (replicate e (natToUnary p) ++ fs)` scales the factor-spine
value by `p^e`. -/
private theorem termValueF_formalTerm_replicate (p e : Nat) (fs : List BHist) :
    termValueF (formalTermFromFactors (List.replicate e (natToUnary p) ++ fs))
      = p ^ e * primeFlatProductNat fs := by
  show primeFlatProductNat (List.replicate e (natToUnary p) ++ fs)
    = p ^ e * primeFlatProductNat fs
  rw [primeFlatProductNat_append, primeFlatProductNat_replicate, natToUnary_length]

/-! ### Shared `Nat` spine of the window enumeration. -/

/-- Multiply every accumulated integer by `p^e` (mirrors `addPrimePowerToTerms` on values). -/
def natAddPrimePower (p e : Nat) : List Nat → List Nat
  | [] => []
  | n :: rest => p ^ e * n :: natAddPrimePower p e rest

/-- Values contributed by a single prime `p` at exponents `0..K` (mirrors
`encodedTermsForPrime`). -/
def natTermsForPrime (p : Nat) : Nat → List Nat → List Nat
  | 0, ns => natAddPrimePower p 0 ns
  | Nat.succ K, ns => natTermsForPrime p K ns ++ natAddPrimePower p (Nat.succ K) ns

/-- The integer values of a finite Euler–Dirichlet window (mirrors `encodedDirichletTerms`). -/
def dirichletValues : List (Nat × Nat) → List Nat
  | [] => [1]
  | (p, K) :: rest => natTermsForPrime p K (dirichletValues rest)

/-! ### Register-side enumeration realizing each Euler term. -/

/-- Prepend the canonical Zeckendorf register `pzgOfExponent p e` to each register (multiplies each
`encodedNat` by `p^e`). -/
def pzgAddPrimePower (p e : Nat) : List PZGRow → List PZGRow
  | [] => []
  | R :: rest => pzgAppend (pzgOfExponent p e) R :: pzgAddPrimePower p e rest

/-- Register terms for a single prime `p` at exponents `0..K`. -/
def pzgEncodedTermsForPrime (p : Nat) : Nat → List PZGRow → List PZGRow
  | 0, regs => pzgAddPrimePower p 0 regs
  | Nat.succ K, regs =>
      pzgEncodedTermsForPrime p K regs ++ pzgAddPrimePower p (Nat.succ K) regs

/-- **The OCLSD register realizing every term of a finite Euler product window** (mirrors Loning's
`encodedDirichletTerms` on the register side). -/
def pzgEncodedDirichlet : List (Nat × Nat) → List PZGRow
  | [] => [PZGRow.nil]
  | (p, K) :: rest => pzgEncodedTermsForPrime p K (pzgEncodedDirichlet rest)

/-! ### Both sides equal the shared `Nat` spine. -/

private theorem map_pzgAddPrimePower (p e : Nat) :
    ∀ regs : List PZGRow,
      (pzgAddPrimePower p e regs).map encodedNat
        = natAddPrimePower p e (regs.map encodedNat)
  | [] => rfl
  | R :: rest => by
      show encodedNat (pzgAppend (pzgOfExponent p e) R)
             :: (pzgAddPrimePower p e rest).map encodedNat
        = p ^ e * encodedNat R :: natAddPrimePower p e (rest.map encodedNat)
      rw [encodedNat_append, encodedNat_pzgOfExponent, map_pzgAddPrimePower p e rest]

private theorem map_addPrimePowerToTerms (p e : Nat) :
    ∀ terms : List FormalEulerTerm,
      (addPrimePowerToTerms p e terms).map termValueF
        = natAddPrimePower p e (terms.map termValueF)
  | [] => rfl
  | term :: terms => by
      show termValueF (formalTermFromFactors (List.replicate e (natToUnary p) ++ term.factors))
             :: (addPrimePowerToTerms p e terms).map termValueF
        = p ^ e * primeFlatProductNat term.factors :: natAddPrimePower p e (terms.map termValueF)
      rw [termValueF_formalTerm_replicate, map_addPrimePowerToTerms p e terms]

private theorem map_pzgEncodedTermsForPrime (p : Nat) :
    ∀ (K : Nat) (regs : List PZGRow),
      (pzgEncodedTermsForPrime p K regs).map encodedNat
        = natTermsForPrime p K (regs.map encodedNat)
  | 0, regs => map_pzgAddPrimePower p 0 regs
  | Nat.succ K, regs => by
      show (pzgEncodedTermsForPrime p K regs ++ pzgAddPrimePower p (Nat.succ K) regs).map encodedNat
        = natTermsForPrime p K (regs.map encodedNat)
            ++ natAddPrimePower p (Nat.succ K) (regs.map encodedNat)
      rw [list_map_append, map_pzgEncodedTermsForPrime p K regs,
        map_pzgAddPrimePower p (Nat.succ K) regs]

private theorem map_encodedTermsForPrime (p : Nat) :
    ∀ (K : Nat) (terms : List FormalEulerTerm),
      (encodedTermsForPrime p K terms).map termValueF
        = natTermsForPrime p K (terms.map termValueF)
  | 0, terms => map_addPrimePowerToTerms p 0 terms
  | Nat.succ K, terms => by
      show (encodedTermsForPrime p K terms ++ addPrimePowerToTerms p (Nat.succ K) terms).map termValueF
        = natTermsForPrime p K (terms.map termValueF)
            ++ natAddPrimePower p (Nat.succ K) (terms.map termValueF)
      rw [list_map_append, map_encodedTermsForPrime p K terms,
        map_addPrimePowerToTerms p (Nat.succ K) terms]

theorem pzgEncodedDirichlet_values :
    ∀ window : List (Nat × Nat),
      (pzgEncodedDirichlet window).map encodedNat = dirichletValues window
  | [] => rfl
  | (p, K) :: rest => by
      show (pzgEncodedTermsForPrime p K (pzgEncodedDirichlet rest)).map encodedNat
        = natTermsForPrime p K (dirichletValues rest)
      rw [map_pzgEncodedTermsForPrime, pzgEncodedDirichlet_values rest]

theorem encodedDirichletTerms_values :
    ∀ window : List (Nat × Nat),
      (encodedDirichletTerms window).map termValueF = dirichletValues window
  | [] => rfl
  | (p, K) :: rest => by
      show (encodedTermsForPrime p K (encodedDirichletTerms rest)).map termValueF
        = natTermsForPrime p K (dirichletValues rest)
      rw [map_encodedTermsForPrime, encodedDirichletTerms_values rest]

/-- **S3 Layer-3 (register = Dirichlet)**: the integer values enumerated by the OCLSD register
finite-window enumeration equal those of Loning's encoded-Dirichlet terms. -/
theorem pzgPartition_eq_encodedDirichlet (window : List (Nat × Nat)) :
    (pzgEncodedDirichlet window).map encodedNat
      = (encodedDirichletTerms window).map termValueF := by
  rw [pzgEncodedDirichlet_values, encodedDirichletTerms_values]

/-- **S3 headline — OCLSD register finite-window partition = finite Euler product.**  The integers
enumerated by the OCLSD Fibonacci/Zeckendorf register over a finite window equal those of the finite
Euler-product expansion `eulerExpandTerms`, by consuming Loning's finite Euler = Dirichlet theorem
`finiteEuler_eq_encodedDirichlet`.  This is the Bost–Connes partition-function correspondence made a
kernel-checked theorem on the OCLSD register — the live S3 link left standing after S1 disproved the
spectral (zero-set) side.  0-axiom; `SpectralZeroIdentity` untouched. -/
theorem pzgPartition_eq_finiteEuler (window : List (Nat × Nat)) :
    (pzgEncodedDirichlet window).map encodedNat
      = (eulerExpandTerms window).map termValueF := by
  rw [pzgPartition_eq_encodedDirichlet, finiteEuler_eq_encodedDirichlet]

end BEDC.Derived.RHRoute.OCLSDRegisterDirichletBridge
