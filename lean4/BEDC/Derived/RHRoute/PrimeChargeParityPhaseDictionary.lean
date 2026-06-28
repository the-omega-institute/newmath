import BEDC.Derived.RHRoute.OddZeroDefect
import BEDC.Derived.RHRoute.PrimePhaseRadialReadback

namespace BEDC.Derived.RHRoute.PrimeChargeParityPhaseDictionary

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.FinitePrimeWindow

abbrev PrimePhaseSample :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseSample

abbrev PrimePhaseRadialStructure :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.PrimePhaseRadialStructure

abbrev RatComplex :=
  BEDC.Derived.RHRoute.PrimePhaseRadialReadback.RatComplex

abbrev NatParity :=
  BEDC.Derived.RHRoute.OddZeroDefect.NatParity

def primeCharge
    (surface : PrimePhaseRadialStructure) (p : Nat) : RatNum :=
  BEDC.Derived.RHRoute.UnitaryBalance.channelAmplitude surface.channel p

def primeParity
    (surface : PrimePhaseRadialStructure) (p : Nat) : NatParity :=
  BEDC.Derived.RHRoute.OddZeroDefect.natParity
    (BEDC.Derived.RHRoute.ZetaInheritedInvariants.logPrimeClock
      surface.clocks p)

structure PrimeChargeParityPhaseEntry where
  prime : Nat
  charge : RatNum
  parity : NatParity
  phase : RatComplex

def entryFromSample
    (surface : PrimePhaseRadialStructure)
    (sample : PrimePhaseSample) : PrimeChargeParityPhaseEntry where
  prime := sample.prime
  charge := primeCharge surface sample.prime
  parity := primeParity surface sample.prime
  phase := sample.phase

def EntryMatchesSurface
    (surface : PrimePhaseRadialStructure)
    (entry : PrimeChargeParityPhaseEntry) : Prop :=
  surface.channel.window.mem entry.prime ∧
    RatEq entry.charge (primeCharge surface entry.prime) ∧
      entry.parity = primeParity surface entry.prime ∧
        ∃ sample : PrimePhaseSample,
          sample ∈ surface.samples ∧
            sample.prime = entry.prime ∧ entry.phase = sample.phase

inductive EntryPrimeNoDup : List PrimeChargeParityPhaseEntry -> Prop where
  | nil : EntryPrimeNoDup []
  | cons {entry : PrimeChargeParityPhaseEntry}
      {entries : List PrimeChargeParityPhaseEntry} :
      ((other : PrimeChargeParityPhaseEntry) ->
        other ∈ entries -> other.prime ≠ entry.prime) ->
        EntryPrimeNoDup entries -> EntryPrimeNoDup (entry :: entries)

def entryPrimeCount (p : Nat) :
    List PrimeChargeParityPhaseEntry -> Nat
  | [] => 0
  | entry :: entries =>
      if p = entry.prime then
        Nat.succ (entryPrimeCount p entries)
      else
        entryPrimeCount p entries

structure PrimeChargeParityPhaseDictionary where
  surface : PrimePhaseRadialStructure
  entries : List PrimeChargeParityPhaseEntry
  key_nodup : EntryPrimeNoDup entries
  entries_match :
    (entry : PrimeChargeParityPhaseEntry) ->
      entry ∈ entries -> EntryMatchesSurface surface entry

namespace EntryPrimeNoDup

theorem count_zero_of_absent {p : Nat} :
    ∀ {entries : List PrimeChargeParityPhaseEntry},
      ((other : PrimeChargeParityPhaseEntry) ->
        other ∈ entries -> other.prime ≠ p) ->
        entryPrimeCount p entries = 0
  | [], _absent => by
      rfl
  | head :: tail, absent => by
      unfold entryPrimeCount
      by_cases same : p = head.prime
      · have headNe : head.prime ≠ p :=
          absent head (List.Mem.head tail)
        exact False.elim (headNe same.symm)
      · rw [if_neg same]
        exact count_zero_of_absent
          (fun other member =>
            absent other (List.Mem.tail head member))

theorem count_eq_one_of_mem_same_prime :
    ∀ {entries : List PrimeChargeParityPhaseEntry},
      EntryPrimeNoDup entries ->
        (entry : PrimeChargeParityPhaseEntry) ->
          entry ∈ entries -> entryPrimeCount entry.prime entries = 1
  | [], nodup, entry, member => by
      cases nodup
      cases member
  | head :: tail, nodup, entry, member => by
      cases nodup with
      | cons absent tailNodup =>
          cases member with
          | head =>
              unfold entryPrimeCount
              rw [if_pos rfl]
              have tailZero :
                  entryPrimeCount head.prime tail = 0 :=
                count_zero_of_absent absent
              rw [tailZero]
          | tail _ tailMember =>
              unfold entryPrimeCount
              by_cases same : entry.prime = head.prime
              · exact False.elim (absent entry tailMember same)
              · rw [if_neg same]
                exact count_eq_one_of_mem_same_prime tailNodup
                  entry tailMember

theorem eq_of_mem_same_prime :
    ∀ {entries : List PrimeChargeParityPhaseEntry},
      EntryPrimeNoDup entries ->
        (left right : PrimeChargeParityPhaseEntry) ->
          left ∈ entries -> right ∈ entries ->
            left.prime = right.prime -> left = right
  | [], nodup, left, _right, leftMem, _rightMem, _samePrime => by
      cases nodup
      cases leftMem
  | entry :: entries, nodup, left, right, leftMem, rightMem, samePrime => by
      cases nodup with
      | cons absent tailNodup =>
          cases leftMem with
          | head =>
              cases rightMem with
              | head =>
                  rfl
              | tail _ rightTail =>
                  exact False.elim (absent right rightTail samePrime.symm)
          | tail _ leftTail =>
              cases rightMem with
              | head =>
                  exact False.elim (absent left leftTail samePrime)
              | tail _ rightTail =>
                  exact eq_of_mem_same_prime tailNodup left right
                    leftTail rightTail samePrime

end EntryPrimeNoDup

def lookupEntry (p : Nat) :
    List PrimeChargeParityPhaseEntry -> Option PrimeChargeParityPhaseEntry
  | [] => none
  | entry :: entries =>
      if p = entry.prime then
        some entry
      else
        lookupEntry p entries

namespace lookupEntry

theorem none_count_zero {p : Nat} :
    ∀ {entries : List PrimeChargeParityPhaseEntry},
      lookupEntry p entries = none ->
        entryPrimeCount p entries = 0
  | [], _notFound => by
      rfl
  | head :: tail, notFound => by
      unfold lookupEntry at notFound
      unfold entryPrimeCount
      by_cases same : p = head.prime
      · rw [if_pos same] at notFound
        cases notFound
      · rw [if_neg same] at notFound
        rw [if_neg same]
        exact none_count_zero notFound

theorem some_mem {p : Nat} :
    ∀ {entries : List PrimeChargeParityPhaseEntry}
      {entry : PrimeChargeParityPhaseEntry},
      lookupEntry p entries = some entry -> entry ∈ entries
  | [], entry, found => by
      cases found
  | head :: tail, entry, found => by
      unfold lookupEntry at found
      by_cases same : p = head.prime
      · rw [if_pos same] at found
        cases found
        exact List.Mem.head tail
      · rw [if_neg same] at found
        exact List.Mem.tail head (some_mem found)

theorem some_prime {p : Nat} :
    ∀ {entries : List PrimeChargeParityPhaseEntry}
      {entry : PrimeChargeParityPhaseEntry},
      lookupEntry p entries = some entry -> entry.prime = p
  | [], entry, found => by
      cases found
  | head :: tail, entry, found => by
      unfold lookupEntry at found
      by_cases same : p = head.prime
      · rw [if_pos same] at found
        cases found
        exact same.symm
      · rw [if_neg same] at found
        exact some_prime found

theorem deterministic
    {p : Nat} {entries : List PrimeChargeParityPhaseEntry}
    {left right : PrimeChargeParityPhaseEntry} :
    lookupEntry p entries = some left ->
      lookupEntry p entries = some right -> left = right := by
  intro leftFound rightFound
  rw [leftFound] at rightFound
  cases rightFound
  rfl

end lookupEntry

namespace PrimeChargeParityPhaseDictionary

def lookup
    (dictionary : PrimeChargeParityPhaseDictionary) (p : Nat) :
    Option PrimeChargeParityPhaseEntry :=
  lookupEntry p dictionary.entries

def primeCount
    (dictionary : PrimeChargeParityPhaseDictionary) (p : Nat) : Nat :=
  entryPrimeCount p dictionary.entries

theorem entry_matches
    (dictionary : PrimeChargeParityPhaseDictionary)
    {entry : PrimeChargeParityPhaseEntry} :
    entry ∈ dictionary.entries ->
      EntryMatchesSurface dictionary.surface entry := by
  intro member
  exact dictionary.entries_match entry member

theorem entry_is_prime
    (dictionary : PrimeChargeParityPhaseDictionary)
    {entry : PrimeChargeParityPhaseEntry} :
    entry ∈ dictionary.entries -> IsPrime entry.prime := by
  intro member
  have row := dictionary.entry_matches member
  exact All.mem dictionary.surface.channel.window.all_prime row.left

theorem entry_charge_eq
    (dictionary : PrimeChargeParityPhaseDictionary)
    {entry : PrimeChargeParityPhaseEntry} :
    entry ∈ dictionary.entries ->
      RatEq entry.charge (primeCharge dictionary.surface entry.prime) := by
  intro member
  exact (dictionary.entry_matches member).right.left

theorem entry_parity_eq
    (dictionary : PrimeChargeParityPhaseDictionary)
    {entry : PrimeChargeParityPhaseEntry} :
    entry ∈ dictionary.entries ->
      entry.parity = primeParity dictionary.surface entry.prime := by
  intro member
  exact (dictionary.entry_matches member).right.right.left

theorem entry_phase_sampled
    (dictionary : PrimeChargeParityPhaseDictionary)
    {entry : PrimeChargeParityPhaseEntry} :
    entry ∈ dictionary.entries ->
      ∃ sample : PrimePhaseSample,
        sample ∈ dictionary.surface.samples ∧
          sample.prime = entry.prime ∧ entry.phase = sample.phase := by
  intro member
  exact (dictionary.entry_matches member).right.right.right

theorem entry_prime_count_one
    (dictionary : PrimeChargeParityPhaseDictionary)
    {entry : PrimeChargeParityPhaseEntry} :
    entry ∈ dictionary.entries ->
      dictionary.primeCount entry.prime = 1 := by
  intro member
  exact EntryPrimeNoDup.count_eq_one_of_mem_same_prime
    dictionary.key_nodup entry member

theorem entries_same_prime_eq
    (dictionary : PrimeChargeParityPhaseDictionary)
    {left right : PrimeChargeParityPhaseEntry} :
    left ∈ dictionary.entries -> right ∈ dictionary.entries ->
      left.prime = right.prime -> left = right := by
  intro leftMember rightMember samePrime
  exact EntryPrimeNoDup.eq_of_mem_same_prime dictionary.key_nodup
    left right leftMember rightMember samePrime

def EntryPayloadEq
    (left right : PrimeChargeParityPhaseEntry) : Prop :=
  RatEq left.charge right.charge ∧
    left.parity = right.parity ∧ left.phase = right.phase

theorem payload_deterministic
    (dictionary : PrimeChargeParityPhaseDictionary)
    {left right : PrimeChargeParityPhaseEntry} :
    left ∈ dictionary.entries -> right ∈ dictionary.entries ->
      left.prime = right.prime -> EntryPayloadEq left right := by
  intro leftMember rightMember samePrime
  have sameEntry :
      left = right :=
    dictionary.entries_same_prime_eq leftMember rightMember samePrime
  cases sameEntry
  exact And.intro (RatEq_refl left.charge) (And.intro rfl rfl)

theorem lookup_mem
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry -> entry ∈ dictionary.entries := by
  intro found
  exact lookupEntry.some_mem found

theorem lookup_requested_prime
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry -> entry.prime = p := by
  intro found
  exact lookupEntry.some_prime found

theorem lookup_is_prime
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry -> IsPrime entry.prime := by
  intro found
  exact dictionary.entry_is_prime (dictionary.lookup_mem found)

theorem lookup_matches
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry ->
      EntryMatchesSurface dictionary.surface entry := by
  intro found
  exact dictionary.entry_matches (dictionary.lookup_mem found)

theorem lookup_prime_count_one
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry ->
      dictionary.primeCount p = 1 := by
  intro found
  have countAtEntry :=
    dictionary.entry_prime_count_one (dictionary.lookup_mem found)
  have samePrime := dictionary.lookup_requested_prime found
  cases samePrime
  exact countAtEntry

theorem lookup_none_prime_count_zero
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} :
    dictionary.lookup p = none -> dictionary.primeCount p = 0 := by
  intro notFound
  exact lookupEntry.none_count_zero notFound

theorem lookup_charge_eq
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry ->
      RatEq entry.charge (primeCharge dictionary.surface p) := by
  intro found
  have charge := dictionary.entry_charge_eq (dictionary.lookup_mem found)
  have samePrime := dictionary.lookup_requested_prime found
  cases samePrime
  exact charge

theorem lookup_parity_eq
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry ->
      entry.parity = primeParity dictionary.surface p := by
  intro found
  have parity := dictionary.entry_parity_eq (dictionary.lookup_mem found)
  have samePrime := dictionary.lookup_requested_prime found
  cases samePrime
  exact parity

theorem lookup_phase_sampled
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {entry : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some entry ->
      ∃ sample : PrimePhaseSample,
        sample ∈ dictionary.surface.samples ∧
          sample.prime = p ∧ entry.phase = sample.phase := by
  intro found
  have sampled := dictionary.entry_phase_sampled (dictionary.lookup_mem found)
  have samePrime := dictionary.lookup_requested_prime found
  cases sampled with
  | intro sample data =>
      cases data with
      | intro sampleMember rest =>
          cases rest with
          | intro samplePrime phaseEq =>
              exact ⟨sample, sampleMember,
                And.intro (samplePrime.trans samePrime) phaseEq⟩

theorem lookup_deterministic
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {left right : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some left ->
      dictionary.lookup p = some right -> left = right := by
  intro leftFound rightFound
  exact lookupEntry.deterministic leftFound rightFound

theorem lookup_payload_deterministic
    (dictionary : PrimeChargeParityPhaseDictionary)
    {p : Nat} {left right : PrimeChargeParityPhaseEntry} :
    dictionary.lookup p = some left ->
      dictionary.lookup p = some right -> EntryPayloadEq left right := by
  intro leftFound rightFound
  have sameEntry := dictionary.lookup_deterministic leftFound rightFound
  cases sameEntry
  exact And.intro (RatEq_refl left.charge) (And.intro rfl rfl)

end PrimeChargeParityPhaseDictionary

def singlePrimeChargeParityPhaseEntry :
    PrimeChargeParityPhaseEntry :=
  entryFromSample
    BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseRadialStructure
    BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseSample

def singlePrimeChargeParityPhaseDictionary :
    PrimeChargeParityPhaseDictionary where
  surface :=
    BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseRadialStructure
  entries := [singlePrimeChargeParityPhaseEntry]
  key_nodup := by
    exact EntryPrimeNoDup.cons
      (by
        intro other member
        cases member)
      EntryPrimeNoDup.nil
  entries_match := by
    intro entry member
    cases member with
    | head =>
        constructor
        · exact List.Mem.head []
        · constructor
          · exact RatEq_refl _
          · constructor
            · rfl
            · exact
                ⟨BEDC.Derived.RHRoute.PrimePhaseRadialReadback.singlePrimePhaseSample,
                  List.Mem.head [], rfl, rfl⟩
    | tail _ tailMember =>
        cases tailMember

theorem singlePrimeChargeParityPhase_lookup_two :
    singlePrimeChargeParityPhaseDictionary.lookup 2 =
      some singlePrimeChargeParityPhaseEntry := by
  rfl

theorem singlePrimeChargeParityPhase_lookup_three_absent :
    singlePrimeChargeParityPhaseDictionary.lookup 3 = none := by
  rfl

theorem singlePrimeChargeParityPhase_entry_prime :
    IsPrime singlePrimeChargeParityPhaseEntry.prime := by
  exact
    singlePrimeChargeParityPhaseDictionary.entry_is_prime
      (List.Mem.head [])

theorem singlePrimeChargeParityPhase_lookup_charge :
    RatEq singlePrimeChargeParityPhaseEntry.charge
      (primeCharge singlePrimeChargeParityPhaseDictionary.surface 2) := by
  exact
    singlePrimeChargeParityPhaseDictionary.lookup_charge_eq
      singlePrimeChargeParityPhase_lookup_two

theorem singlePrimeChargeParityPhase_lookup_parity :
    singlePrimeChargeParityPhaseEntry.parity =
      primeParity singlePrimeChargeParityPhaseDictionary.surface 2 := by
  exact
    singlePrimeChargeParityPhaseDictionary.lookup_parity_eq
      singlePrimeChargeParityPhase_lookup_two

end BEDC.Derived.RHRoute.PrimeChargeParityPhaseDictionary
