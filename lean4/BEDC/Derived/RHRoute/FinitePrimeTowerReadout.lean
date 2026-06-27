import BEDC.Derived.RHRoute.ChannelNormalForm
import BEDC.Derived.RHRoute.RecursiveTower

namespace BEDC.Derived.RHRoute.FinitePrimeTowerReadout

open BEDC.Derived.RHRoute.FinitePrimeWindow

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev IsPrime := BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime
abbrev RecursivePrimeWindowTower :=
  BEDC.Derived.RHRoute.RecursiveTower.PrimeWindowTower

def extendWindow (W : PrimeWindow) (p : Nat) (prime : IsPrime p) :
    PrimeWindow where
  elems := insertFreshNat p W.elems
  nodup := nodup_insertFreshNat W.nodup
  all_prime := all_prime_insertFreshNat prime W.all_prime

theorem extendWindow_mem_self (W : PrimeWindow) (p : Nat)
    (prime : IsPrime p) :
    PrimeWindow.mem p (extendWindow W p prime) := by
  exact mem_insertFreshNat_self p W.elems

theorem extendWindow_mem_old (W : PrimeWindow) (p q : Nat)
    (prime : IsPrime p) :
    PrimeWindow.mem q W -> PrimeWindow.mem q (extendWindow W p prime) := by
  intro member
  exact mem_insertFreshNat_of_mem member

theorem extendWindow_member_prime (W : PrimeWindow) (p q : Nat)
    (prime : IsPrime p) :
    PrimeWindow.mem q (extendWindow W p prime) -> IsPrime q := by
  intro member
  exact All.mem (extendWindow W p prime).all_prime member

def extendElems : List Nat -> List Nat -> List Nat
  | elems, [] => elems
  | elems, p :: ps => extendElems (insertFreshNat p elems) ps

theorem nodup_extendElems :
    ∀ {elems primes : List Nat},
      NoDup elems -> NoDup (extendElems elems primes)
  | _elems, [], nodup => nodup
  | elems, _p :: ps, nodup => by
      exact nodup_extendElems (elems := insertFreshNat _p elems) (primes := ps)
        (nodup_insertFreshNat nodup)

theorem all_prime_extendElems :
    ∀ {elems primes : List Nat},
      All IsPrime elems -> All IsPrime primes ->
        All IsPrime (extendElems elems primes)
  | _elems, [], allElems, _allPrimes => allElems
  | elems, _p :: ps, allElems, allPrimes => by
      cases allPrimes with
      | cons pPrime psPrime =>
          exact all_prime_extendElems
            (elems := insertFreshNat _p elems) (primes := ps)
            (all_prime_insertFreshNat pPrime allElems) psPrime

def extendWindowList (base : PrimeWindow) (primes : List Nat)
    (primesPrime : All IsPrime primes) : PrimeWindow where
  elems := extendElems base.elems primes
  nodup := nodup_extendElems base.nodup
  all_prime := all_prime_extendElems base.all_prime primesPrime

theorem extendWindowList_mem_base :
    ∀ (base : PrimeWindow) (primes : List Nat)
      (primesPrime : All IsPrime primes) (p : Nat),
        PrimeWindow.mem p base ->
          PrimeWindow.mem p (extendWindowList base primes primesPrime)
  | _base, [], _primesPrime, _p, member => member
  | base, q :: qs, allPrimes, p, member => by
      cases allPrimes with
      | cons qPrime qsPrime =>
          exact extendWindowList_mem_base (extendWindow base q qPrime) qs qsPrime p
            (extendWindow_mem_old base q p qPrime member)

theorem extendWindowList_mem_added :
    ∀ (base : PrimeWindow) (primes : List Nat)
      (primesPrime : All IsPrime primes) (p : Nat),
        p ∈ primes -> PrimeWindow.mem p (extendWindowList base primes primesPrime)
  | _base, [], _primesPrime, _p, member => by
      cases member
  | base, q :: qs, allPrimes, p, member => by
      cases allPrimes with
      | cons qPrime qsPrime =>
          cases member with
          | head =>
              exact extendWindowList_mem_base (extendWindow base q qPrime) qs qsPrime q
                (extendWindow_mem_self base q qPrime)
          | tail _ tailMember =>
              exact extendWindowList_mem_added (extendWindow base q qPrime) qs qsPrime p
                tailMember

structure FinitePrimeTower where
  base : PrimeWindow
  additions : List Nat
  additions_prime : All IsPrime additions

namespace FinitePrimeTower

def completedWindow (T : FinitePrimeTower) : PrimeWindow :=
  extendWindowList T.base T.additions T.additions_prime

def layerCount (T : FinitePrimeTower) : Nat :=
  T.additions.length

theorem base_mem_completed (T : FinitePrimeTower) {p : Nat} :
    PrimeWindow.mem p T.base -> PrimeWindow.mem p T.completedWindow := by
  intro member
  exact extendWindowList_mem_base T.base T.additions T.additions_prime p member

theorem addition_mem_completed (T : FinitePrimeTower) {p : Nat} :
    p ∈ T.additions -> PrimeWindow.mem p T.completedWindow := by
  intro member
  exact extendWindowList_mem_added T.base T.additions T.additions_prime p member

theorem completed_member_prime (T : FinitePrimeTower) {p : Nat} :
    PrimeWindow.mem p T.completedWindow -> IsPrime p := by
  intro member
  exact All.mem T.completedWindow.all_prime member

end FinitePrimeTower

inductive ReadoutEvent where
  | seedWindow : Nat -> ReadoutEvent
  | extendPrime : Nat -> ReadoutEvent
  | completedWindow : Nat -> ReadoutEvent

def extensionTrace : List Nat -> List ReadoutEvent
  | [] => []
  | p :: ps => ReadoutEvent.extendPrime p :: extensionTrace ps

def readoutTrace (T : FinitePrimeTower) : List ReadoutEvent :=
  ReadoutEvent.seedWindow T.base.elems.length ::
    extensionTrace T.additions ++
      [ReadoutEvent.completedWindow T.completedWindow.elems.length]

structure CompletedReadoutFor (T : FinitePrimeTower) where
  window : PrimeWindow
  completed : window.elems = T.completedWindow.elems

def completedReadout (T : FinitePrimeTower) : CompletedReadoutFor T where
  window := T.completedWindow
  completed := rfl

structure CompletedPrimeTowerReadoutFor (T : FinitePrimeTower) where
  readout : CompletedReadoutFor T
  trace : List ReadoutEvent
  trace_ok : trace = readoutTrace T

def completedPrimeTowerReadout (T : FinitePrimeTower) :
    CompletedPrimeTowerReadoutFor T where
  readout := completedReadout T
  trace := readoutTrace T
  trace_ok := rfl

theorem completed_readout_deterministic {T : FinitePrimeTower}
    (left right : CompletedReadoutFor T) :
    left.window.elems = right.window.elems := by
  exact Eq.trans left.completed (Eq.symm right.completed)

theorem completed_prime_tower_readout_deterministic {T : FinitePrimeTower}
    (left right : CompletedPrimeTowerReadoutFor T) :
    left.readout.window.elems = right.readout.window.elems ∧
      left.trace = right.trace := by
  exact And.intro
    (completed_readout_deterministic left.readout right.readout)
    (Eq.trans left.trace_ok (Eq.symm right.trace_ok))

theorem completed_readout_window_nodup {T : FinitePrimeTower}
    (readout : CompletedReadoutFor T) :
    NoDup readout.window.elems := by
  rw [readout.completed]
  exact T.completedWindow.nodup

theorem completed_readout_window_all_prime {T : FinitePrimeTower}
    (readout : CompletedReadoutFor T) :
    All IsPrime readout.window.elems := by
  rw [readout.completed]
  exact T.completedWindow.all_prime

theorem completed_readout_member_prime {T : FinitePrimeTower}
    (readout : CompletedReadoutFor T) {p : Nat} :
    PrimeWindow.mem p readout.window -> IsPrime p := by
  intro member
  have terminalMember : PrimeWindow.mem p T.completedWindow := by
    unfold PrimeWindow.mem
    rw [← readout.completed]
    exact member
  exact T.completed_member_prime terminalMember

def completedReadoutFingerprint (T : FinitePrimeTower) :
    BEDC.Derived.RHRoute.ChannelNormalForm.Fingerprint
      (CompletedReadoutFor T) where
  window := T.completedWindow
  encode := fun readout => readout.window.elems
  normalized := fun readout => readout.window.elems = T.completedWindow.elems

theorem completed_readout_fingerprint_deterministic {T : FinitePrimeTower}
    (left right : CompletedReadoutFor T) :
    BEDC.Derived.RHRoute.ChannelNormalForm.FingerprintEq
      (completedReadoutFingerprint T) left right := by
  exact completed_readout_deterministic left right

end BEDC.Derived.RHRoute.FinitePrimeTowerReadout
