import BEDC.Derived.FibonacciUp
import BEDC.Derived.MatrixUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GoldenMeanShiftUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GoldenMeanShiftCarrier [AskSetup] [PackageSetup]
    (window zeroWitness adjacencyLedger provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory zeroWitness ∧ UnaryHistory adjacencyLedger ∧
    UnaryHistory provenance ∧ UnaryHistory ledger ∧ Cont window zeroWitness adjacencyLedger ∧
      Cont adjacencyLedger provenance ledger ∧ Cont ledger zeroWitness endpoint ∧
        PkgSig bundle endpoint pkg

theorem GoldenMeanShiftCarrier_local_stability [AskSetup] [PackageSetup]
    {window zeroWitness adjacencyLedger provenance ledger endpoint window' zeroWitness'
      adjacencyLedger' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
        bundle pkg ->
      hsame window window' ->
        hsame zeroWitness zeroWitness' ->
          hsame adjacencyLedger adjacencyLedger' ->
            hsame provenance provenance' ->
              hsame ledger ledger' ->
                hsame endpoint endpoint' ->
                  Cont window' zeroWitness' adjacencyLedger' ->
                    Cont adjacencyLedger' provenance' ledger' ->
                      Cont ledger' zeroWitness' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          GoldenMeanShiftCarrier window' zeroWitness' adjacencyLedger'
                              provenance' ledger' endpoint' bundle pkg ∧
                            hsame endpoint endpoint' := by
  intro carrier sameWindow sameZero sameAdjacency sameProvenance sameLedger sameEndpoint
    transportedFirst transportedSecond transportedEndpoint transportedPkg
  obtain ⟨windowUnary, zeroUnary, adjacencyUnary, provenanceUnary, ledgerUnary,
    _firstCont, _secondCont, _endpointCont, _endpointPkg⟩ := carrier
  exact
    ⟨⟨unary_transport windowUnary sameWindow,
        unary_transport zeroUnary sameZero,
        unary_transport adjacencyUnary sameAdjacency,
        unary_transport provenanceUnary sameProvenance,
        unary_transport ledgerUnary sameLedger,
        transportedFirst,
        transportedSecond,
        transportedEndpoint,
        transportedPkg⟩,
      sameEndpoint⟩

theorem GoldenMeanShiftCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {window zeroWitness adjacencyLedger provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
            bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem GoldenMeanShiftUp_StdBridge [AskSetup] [PackageSetup]
    {window zeroWitness adjacencyLedger provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
        bundle pkg ->
      Cont window zeroWitness adjacencyLedger ∧
        Cont adjacencyLedger provenance ledger ∧
          Cont ledger zeroWitness endpoint ∧
            hsame endpoint (append ledger zeroWitness) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  rcases carrier with
    ⟨_windowUnary, _zeroUnary, _adjacencyUnary, _provenanceUnary, _ledgerUnary,
      windowRow, ledgerRow, endpointRow, pkgSig⟩
  have endpointSame : hsame endpoint (append ledger zeroWitness) := by
    cases endpointRow
    rfl
  exact And.intro windowRow
    (And.intro ledgerRow (And.intro endpointRow (And.intro endpointSame pkgSig)))

inductive Bit where
  | zero
  | one
deriving DecidableEq

inductive AllowedPair : Bit -> Bit -> Prop where
  | zero_zero : AllowedPair Bit.zero Bit.zero
  | zero_one : AllowedPair Bit.zero Bit.one
  | one_zero : AllowedPair Bit.one Bit.zero

abbrev allowedPair : Bit -> Bit -> Prop :=
  AllowedPair

inductive AllowedWord : List Bit -> Prop where
  | nil : AllowedWord []
  | single (a : Bit) : AllowedWord [a]
  | cons {a b : Bit} {tail : List Bit} :
      allowedPair a b -> AllowedWord (b :: tail) ->
        AllowedWord (a :: b :: tail)

abbrev allowedWord : List Bit -> Prop :=
  AllowedWord

def allowedFrom (previous : Bit) : List Bit -> Prop
  | [] => allowedWord [previous]
  | b :: tail => allowedPair previous b ∧ allowedFrom b tail

abbrev GoldenSequence : Type :=
  Nat -> Bit

def sequenceAllowed (x : GoldenSequence) : Prop :=
  (n : Nat) -> allowedPair (x n) (x (n + 1))

def sigma (x : GoldenSequence) : GoldenSequence :=
  fun n => x (n + 1)

structure GoldenCountState where
  total : Nat
  zeroLast : Nat

def countStep : GoldenCountState -> GoldenCountState
  | ⟨total, zeroLast⟩ => ⟨total + zeroLast, total⟩

def countState : Nat -> GoldenCountState
  | 0 => ⟨1, 1⟩
  | n + 1 => countStep (countState n)

def allowedCount (n : Nat) : Nat :=
  (countState n).total

def zeroTerminalAllowedCount (n : Nat) : Nat :=
  (countState n).zeroLast

def continuationCount : Bit -> Nat -> Nat
  | Bit.zero, n => allowedCount n
  | Bit.one, 0 => 1
  | Bit.one, n + 1 => allowedCount n

def prefixBit (b : Bit) : List (List Bit) -> List (List Bit)
  | [] => []
  | word :: rest => (b :: word) :: prefixBit b rest

def continuations : Bit -> Nat -> List (List Bit)
  | _, 0 => [[]]
  | Bit.zero, n + 1 =>
      prefixBit Bit.one (continuations Bit.one n) ++
        prefixBit Bit.zero (continuations Bit.zero n)
  | Bit.one, n + 1 => prefixBit Bit.zero (continuations Bit.zero n)

def allowedWords : Nat -> List (List Bit)
  | 0 => [[]]
  | n + 1 =>
      prefixBit Bit.one (continuations Bit.one n) ++
        prefixBit Bit.zero (continuations Bit.zero n)

def goldenKernel : BEDC.Derived.Window6Transfer.Mat2 :=
  BEDC.Derived.Window6Transfer.M

def goldenKernelEntry : Bit -> Bit -> Int
  | Bit.zero, Bit.zero => goldenKernel.a
  | Bit.zero, Bit.one => goldenKernel.b
  | Bit.one, Bit.zero => goldenKernel.c
  | Bit.one, Bit.one => goldenKernel.d

theorem goldenKernel_entries :
    goldenKernel = ⟨1, 1, 1, 0⟩ := by
  rfl

theorem allowedPair_not_one_one :
    allowedPair Bit.one Bit.one -> False := by
  intro h
  cases h

theorem allowedPair_zero_left (b : Bit) :
    allowedPair Bit.zero b := by
  cases b with
  | zero => exact AllowedPair.zero_zero
  | one => exact AllowedPair.zero_one

theorem allowedPair_one_right_zero :
    allowedPair Bit.one Bit.zero := by
  exact AllowedPair.one_zero

theorem goldenKernelEntry_allowed {a b : Bit} :
    allowedPair a b -> goldenKernelEntry a b = 1 := by
  intro h
  cases h <;> rfl

theorem goldenKernelEntry_forbidden_one_one :
    goldenKernelEntry Bit.one Bit.one = 0 := by
  rfl

theorem goldenKernelEntry_one_implies_allowed (a b : Bit) :
    goldenKernelEntry a b = 1 -> allowedPair a b := by
  cases a with
  | zero =>
      cases b with
      | zero =>
          intro _h
          exact AllowedPair.zero_zero
      | one =>
          intro _h
          exact AllowedPair.zero_one
  | one =>
      cases b with
      | zero =>
          intro _h
          exact AllowedPair.one_zero
      | one =>
          intro h
          cases h

theorem goldenKernelEntry_eq_one_iff_allowed (a b : Bit) :
    goldenKernelEntry a b = 1 ↔ allowedPair a b := by
  constructor
  · exact goldenKernelEntry_one_implies_allowed a b
  · exact goldenKernelEntry_allowed

theorem allowedWord_tail {a : Bit} {w : List Bit} :
    allowedWord (a :: w) -> allowedWord w := by
  intro h
  cases h with
  | single a =>
      exact AllowedWord.nil
  | cons pair rest =>
      exact rest

def shiftLeft : List Bit -> List Bit
  | [] => []
  | _ :: tail => tail

theorem shiftLeft_preserves_allowed (w : List Bit) :
    allowedWord w -> allowedWord (shiftLeft w) := by
  cases w with
  | nil =>
      intro h
      exact h
  | cons a tail =>
      exact allowedWord_tail

theorem sigma_preserves_sequenceAllowed (x : GoldenSequence) :
    sequenceAllowed x -> sequenceAllowed (sigma x) := by
  intro h n
  exact h (n + 1)

theorem allowedCount_zero :
    allowedCount 0 = 1 := by
  rfl

theorem allowedCount_one :
    allowedCount 1 = 2 := by
  rfl

theorem allowedCount_recurrence (n : Nat) :
    allowedCount (n + 2) = allowedCount (n + 1) + allowedCount n := by
  rfl

theorem allowedCount_first_symbol_split (n : Nat) :
    allowedCount (n + 1) =
      continuationCount Bit.zero n + continuationCount Bit.one n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

theorem prefixBit_length (b : Bit) (words : List (List Bit)) :
    (prefixBit b words).length = words.length := by
  induction words with
  | nil =>
      rfl
  | cons word rest ih =>
      change Nat.succ (prefixBit b rest).length = Nat.succ rest.length
      exact congrArg Nat.succ ih

private theorem append_length_right_first {α : Type} (xs ys : List α) :
    (xs ++ ys).length = ys.length + xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change Nat.succ ((xs ++ ys).length) = Nat.succ (ys.length + xs.length)
      exact congrArg Nat.succ ih

theorem continuations_length_eq_count (b : Bit) (n : Nat) :
    (continuations b n).length = continuationCount b n := by
  induction n generalizing b with
  | zero =>
      cases b <;> rfl
  | succ n ih =>
      cases b with
      | zero =>
          change
            (prefixBit Bit.one (continuations Bit.one n) ++
                prefixBit Bit.zero (continuations Bit.zero n)).length =
              allowedCount (n + 1)
          rw [append_length_right_first]
          rw [prefixBit_length, prefixBit_length]
          rw [ih Bit.zero, ih Bit.one]
          exact (allowedCount_first_symbol_split n).symm
      | one =>
          change (prefixBit Bit.zero (continuations Bit.zero n)).length = allowedCount n
          rw [prefixBit_length]
          exact ih Bit.zero

theorem allowedWords_length_eq_count (n : Nat) :
    (allowedWords n).length = allowedCount n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      change
        (prefixBit Bit.one (continuations Bit.one n) ++
            prefixBit Bit.zero (continuations Bit.zero n)).length =
          allowedCount (n + 1)
      rw [append_length_right_first]
      rw [prefixBit_length, prefixBit_length]
      rw [continuations_length_eq_count Bit.zero n]
      rw [continuations_length_eq_count Bit.one n]
      exact (allowedCount_first_symbol_split n).symm

theorem countState_eq_fib_pair (n : Nat) :
    countState n =
      ⟨BEDC.Derived.FibonacciUp.fib (n + 2),
        BEDC.Derived.FibonacciUp.fib (n + 1)⟩ := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [countState, ih]
      rfl

theorem allowedCount_eq_fib_shift (n : Nat) :
    allowedCount n = BEDC.Derived.FibonacciUp.fib (n + 2) := by
  unfold allowedCount
  rw [countState_eq_fib_pair n]

theorem finite_window_count_eq_fibonacci (n : Nat) :
    allowedCount n = BEDC.Derived.FibonacciUp.fib (n + 2) :=
  allowedCount_eq_fib_shift n

theorem allowedWords_length_eq_fibonacci (n : Nat) :
    (allowedWords n).length = BEDC.Derived.FibonacciUp.fib (n + 2) := by
  rw [allowedWords_length_eq_count n]
  exact allowedCount_eq_fib_shift n

theorem prefixBit_mem_shape (b : Bit) (words : List (List Bit)) {w : List Bit} :
    w ∈ prefixBit b words -> ∃ tail, w = b :: tail ∧ tail ∈ words := by
  induction words with
  | nil =>
      intro h
      cases h
  | cons word rest ih =>
      intro h
      cases h with
      | head =>
          exact Exists.intro word (And.intro rfl (List.Mem.head rest))
      | tail head htail =>
          obtain ⟨tail, eqw, memTail⟩ := ih htail
          exact Exists.intro tail (And.intro eqw (List.Mem.tail word memTail))

private theorem mem_append_split {α : Type} (xs ys : List α) {a : α} :
    a ∈ xs ++ ys -> a ∈ xs ∨ a ∈ ys := by
  induction xs with
  | nil =>
      intro h
      exact Or.inr h
  | cons x xs ih =>
      intro h
      cases h with
      | head =>
          exact Or.inl (List.Mem.head xs)
      | tail head htail =>
          have split := ih htail
          cases split with
          | inl inLeft =>
              exact Or.inl (List.Mem.tail x inLeft)
          | inr inRight =>
              exact Or.inr inRight

theorem allowedFrom_to_allowedWord (b : Bit) (tail : List Bit) :
    allowedFrom b tail -> allowedWord (b :: tail) := by
  induction tail generalizing b with
  | nil =>
      intro h
      exact h
  | cons c rest ih =>
      intro h
      exact AllowedWord.cons h.left (ih c h.right)

theorem continuations_sound (b : Bit) (n : Nat) {tail : List Bit} :
    tail ∈ continuations b n -> allowedFrom b tail := by
  induction n generalizing b tail with
  | zero =>
      cases b with
      | zero =>
          intro h
          cases h with
          | head =>
              exact AllowedWord.single Bit.zero
          | tail head htail =>
              cases htail
      | one =>
          intro h
          cases h with
          | head =>
              exact AllowedWord.single Bit.one
          | tail head htail =>
              cases htail
  | succ n ih =>
      cases b with
      | zero =>
          intro h
          change tail ∈
            (prefixBit Bit.one (continuations Bit.one n) ++
              prefixBit Bit.zero (continuations Bit.zero n)) at h
          have split :=
            mem_append_split (prefixBit Bit.one (continuations Bit.one n))
              (prefixBit Bit.zero (continuations Bit.zero n)) h
          cases split with
          | inl leftMem =>
              obtain ⟨rest, eqTail, memRest⟩ :=
                prefixBit_mem_shape Bit.one (continuations Bit.one n) leftMem
              cases eqTail
              exact And.intro AllowedPair.zero_one (ih Bit.one memRest)
          | inr rightMem =>
              obtain ⟨rest, eqTail, memRest⟩ :=
                prefixBit_mem_shape Bit.zero (continuations Bit.zero n) rightMem
              cases eqTail
              exact And.intro AllowedPair.zero_zero (ih Bit.zero memRest)
      | one =>
          intro h
          change tail ∈ prefixBit Bit.zero (continuations Bit.zero n) at h
          obtain ⟨rest, eqTail, memRest⟩ :=
            prefixBit_mem_shape Bit.zero (continuations Bit.zero n) h
          cases eqTail
          exact And.intro AllowedPair.one_zero (ih Bit.zero memRest)

theorem allowedWords_sound (n : Nat) {w : List Bit} :
    w ∈ allowedWords n -> allowedWord w := by
  cases n with
  | zero =>
      intro h
      cases h with
      | head =>
          exact AllowedWord.nil
      | tail head htail =>
          cases htail
  | succ n =>
      intro h
      change w ∈
        (prefixBit Bit.one (continuations Bit.one n) ++
          prefixBit Bit.zero (continuations Bit.zero n)) at h
      have split :=
        mem_append_split (prefixBit Bit.one (continuations Bit.one n))
          (prefixBit Bit.zero (continuations Bit.zero n)) h
      cases split with
      | inl leftMem =>
          obtain ⟨tail, eqW, memTail⟩ :=
            prefixBit_mem_shape Bit.one (continuations Bit.one n) leftMem
          cases eqW
          exact allowedFrom_to_allowedWord Bit.one tail (continuations_sound Bit.one n memTail)
      | inr rightMem =>
          obtain ⟨tail, eqW, memTail⟩ :=
            prefixBit_mem_shape Bit.zero (continuations Bit.zero n) rightMem
          cases eqW
          exact allowedFrom_to_allowedWord Bit.zero tail (continuations_sound Bit.zero n memTail)

theorem allowedFrom_cons (a b : Bit) (tail : List Bit) :
    allowedFrom a (b :: tail) -> allowedPair a b ∧ allowedFrom b tail := by
  intro h
  exact h

theorem allowedWord_cons_cons (a b : Bit) (tail : List Bit) :
    allowedWord (a :: b :: tail) ->
      allowedPair a b ∧ allowedWord (b :: tail) := by
  intro h
  cases h with
  | cons pair rest =>
      exact And.intro pair rest

theorem allowedWord_pair_cons {a b : Bit} {tail : List Bit} :
    allowedPair a b -> allowedWord (b :: tail) ->
      allowedWord (a :: b :: tail) := by
  intro pair rest
  exact AllowedWord.cons pair rest

theorem zero_terminal_count_eq_fib (n : Nat) :
    zeroTerminalAllowedCount n = BEDC.Derived.FibonacciUp.fib (n + 1) := by
  unfold zeroTerminalAllowedCount
  rw [countState_eq_fib_pair n]

theorem goldenKernel_transfer_power_fib (n : Nat) :
    BEDC.Derived.Window6Transfer.npow goldenKernel (n + 1) =
      ⟨((BEDC.Derived.FibonacciUp.fib (n + 2) : Nat) : Int),
        ((BEDC.Derived.FibonacciUp.fib (n + 1) : Nat) : Int),
        ((BEDC.Derived.FibonacciUp.fib (n + 1) : Nat) : Int),
        ((BEDC.Derived.FibonacciUp.fib n : Nat) : Int)⟩ := by
  exact BEDC.Derived.FibonacciUp.transfer_power_fib n

theorem allowedFrom_cons_iff (a b : Bit) (tail : List Bit) :
    allowedFrom a (b :: tail) ↔ allowedPair a b ∧ allowedFrom b tail := by
  constructor
  · exact allowedFrom_cons a b tail
  · intro h
    exact h

theorem allowedWord_cons_cons_iff (a b : Bit) (tail : List Bit) :
    allowedWord (a :: b :: tail) ↔
      allowedPair a b ∧ allowedWord (b :: tail) := by
  constructor
  · exact allowedWord_cons_cons a b tail
  · intro h
    exact allowedWord_pair_cons h.left h.right

theorem allowedFrom_cons_definal (a b : Bit) (tail : List Bit) :
    allowedFrom a (b :: tail) = (allowedPair a b ∧ allowedFrom b tail) := by
  rfl

end BEDC.Derived.GoldenMeanShiftUp
