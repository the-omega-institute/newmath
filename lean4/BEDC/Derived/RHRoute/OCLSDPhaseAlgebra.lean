import BEDC.Derived.RHRoute.LocatedGenerationTower

/-
ζ-free prime-phase leverage (oracle conv_ff4ff126afd06e33, 2026-07-02).

Verdict on "OCLSD ≡ zeta dynamics": NOT 100% wall. From the tick dynamics +
Prime–Zeckendorf–Gödel register one can derive, **ζ-free**, the formal prime-phase
character factorization
  n^{-s} = n^{-σ} e^{-i t θ(n)},  θ(n) = Σ_{p,k} z_{p,k} F_k log p,
  χ_t(n) = e^{-i t θ(n)} = Π_{p,k} e^{-i t z_{p,k} F_k log p}.
What stays a wall is only "formal spectrum = TRUE zeta-zero spectrum" (Hilbert–Pólya).

This module builds the ζ-free half: a `FormalPhaseAlgebra` (the phase/character
target, Type-valued `Eqv`, propext-free) + the PZG register readback + the
character factorization theorem `readPZGPhase_append` (χ_t multiplicative over
register concatenation) proved from monoid laws. No zeta evaluator appears.

anti-backward-fit: the phase of an atom is `primePhase p k` — a function of the
prime id and Fibonacci index ONLY, never an external angle input, so the phase is
prime-locked and cannot be tuned to zeta zero heights.
-/

namespace BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-- Formal phase/character algebra: the target of the PZG readback. `Eqv` is
Type-valued (propext-free). `primePhase p k` is the formal atom phase
$e^{-i t F_k \log p}$ — a function of $(p,k)$ only (prime-locked). -/
structure FormalPhaseAlgebra where
  Phase : Type
  Eqv : Phase → Phase → Type
  one : Phase
  mul : Phase → Phase → Phase
  primePhase : Nat → Nat → Phase

/-- A Prime–Zeckendorf–Gödel register row: a finite list of activated
$(prime, \text{Fibonacci-index})$ atoms, i.e. the $(p,k)$ with $z_{p,k}=1$. -/
inductive PZGRow where
  | nil : PZGRow
  | cons : Nat → Nat → PZGRow → PZGRow

/-- PZG phase readback: multiply the prime-phase of each activated atom,
$\mathrm{read}(z) = \prod_{(p,k)} \mathrm{primePhase}(p,k)$. Structural recursion. -/
def readPZGPhase (A : FormalPhaseAlgebra) : PZGRow → A.Phase
  | PZGRow.nil => A.one
  | PZGRow.cons p k rest => A.mul (A.primePhase p k) (readPZGPhase A rest)

theorem readPZGPhase_nil (A : FormalPhaseAlgebra) :
    readPZGPhase A PZGRow.nil = A.one := rfl

/-- Forward factorization for one activated atom (one tick): a fresh atom
multiplies in exactly its prime phase, $\chi_t = \mathrm{primePhase}(p,k)\cdot\chi_t'$.
`rfl`, ζ-free. -/
theorem readPZGPhase_tick (A : FormalPhaseAlgebra) (p k : Nat) (rest : PZGRow) :
    readPZGPhase A (PZGRow.cons p k rest)
      = A.mul (A.primePhase p k) (readPZGPhase A rest) := rfl

/-- Register concatenation. -/
def pzgAppend : PZGRow → PZGRow → PZGRow
  | PZGRow.nil, ys => ys
  | PZGRow.cons p k xs, ys => PZGRow.cons p k (pzgAppend xs ys)

/-- Monoid laws on the phase algebra, stated through the Type-valued `Eqv`
(propext-free): reflexivity, transitivity, `mul` congruence, left unit, and
associativity. This is exactly the structure a phase/character group supplies. -/
structure PhaseMonoidLaws (A : FormalPhaseAlgebra) where
  reflE : (x : A.Phase) → A.Eqv x x
  transE : {x y z : A.Phase} → A.Eqv x y → A.Eqv y z → A.Eqv x z
  mulCongr : {a a' b b' : A.Phase} →
    A.Eqv a a' → A.Eqv b b' → A.Eqv (A.mul a b) (A.mul a' b')
  oneMul : (x : A.Phase) → A.Eqv (A.mul A.one x) x
  mulAssoc : (x y z : A.Phase) →
    A.Eqv (A.mul (A.mul x y) z) (A.mul x (A.mul y z))

/-- **Character factorization** (ζ-free): the PZG phase readback is multiplicative
over register concatenation, $\chi_t(m\,n) \sim \chi_t(m)\,\chi_t(n)$. Proved by
structural induction on the first register using only the monoid laws. -/
def readPZGPhase_append (A : FormalPhaseAlgebra) (L : PhaseMonoidLaws A) :
    ∀ xs ys : PZGRow,
      A.Eqv (A.mul (readPZGPhase A xs) (readPZGPhase A ys))
        (readPZGPhase A (pzgAppend xs ys))
  | PZGRow.nil, ys => L.oneMul (readPZGPhase A ys)
  | PZGRow.cons p k xs, ys =>
      L.transE
        (L.mulAssoc (A.primePhase p k) (readPZGPhase A xs) (readPZGPhase A ys))
        (L.mulCongr (L.reflE (A.primePhase p k))
          (readPZGPhase_append A L xs ys))

/-! ### Non-vacuity: a concrete phase algebra that computes -/

/-- Toy concrete phase algebra: `Phase := Nat`, `Eqv := PLift ∘ Eq`, additive
"phase" with `primePhase p k := p + k`. Certifies the interface is inhabited and
the readback computes. -/
def toyPhase : FormalPhaseAlgebra where
  Phase := Nat
  Eqv := fun a b => PLift (a = b)
  one := 0
  mul := Nat.add
  primePhase := fun p k => p + k

/-- Concrete computation (rfl): reading `(2,1)(3,0)` in `toyPhase` gives
$(2+1)+((3+0)+0)=6$. Non-vacuous. -/
theorem toyPhase_reads :
    readPZGPhase toyPhase
        (PZGRow.cons 2 1 (PZGRow.cons 3 0 PZGRow.nil)) = (6 : Nat) := rfl

end BEDC.Derived.RHRoute.OCLSDPhaseAlgebra
