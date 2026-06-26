import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.PhiDivisorSum

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

def phiFactorListSumNat : List (List BHist) -> Nat
  | [] => 0
  | fs :: fss => eulerPhiFactorsNat fs + phiFactorListSumNat fss

def profileDivisorFactorLists : PrimePowerProfile -> List (List BHist)
  | [] => [[]]
  | e :: es =>
      appendFactorListProducts
        (primePowerFactorLists e.prime e.exponent)
        (profileDivisorFactorLists es)

def profilePhiDivisorSumNat (profile : PrimePowerProfile) : Nat :=
  phiFactorListSumNat (profileDivisorFactorLists profile)

def profileProductNat : PrimePowerProfile -> Nat
  | [] => 1
  | e :: es => natPow (bwordLength e.prime) e.exponent * profileProductNat es

def profilePhiDivisorSum (profile : PrimePowerProfile) : BHist :=
  natToUnary (profilePhiDivisorSumNat profile)

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem nat_add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.mul_add c a b
    _ = a * c + c * b := congrArg (fun x => x + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun x => a * c + x) (Nat.mul_comm c b)

private theorem nat_mul_left_comm_pure (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := (nat_mul_assoc_pure a b c).symm
    _ = (b * a) * c := congrArg (fun t => t * c) (Nat.mul_comm a b)
    _ = b * (a * c) := nat_mul_assoc_pure b a c

private theorem nat_add_congr_pure
    {a b c d : Nat} :
    a = b -> c = d -> a + c = b + d := by
  intro left right
  cases left
  cases right
  rfl

private theorem nat_one_add_pred_of_pos {n : Nat} :
    0 < n -> 1 + (n - 1) = n := by
  intro positive
  cases n with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 positive)
  | succ n =>
      rw [Nat.succ_sub_succ]
      rw [Nat.sub_zero]
      exact Nat.add_comm 1 n

private theorem natPrime_length_pos {p : BHist} :
    NatPrime p -> 0 < bwordLength p := by
  intro pPrime
  cases p with
  | Empty =>
      exact False.elim (NatUnaryStrictPrefix_empty_right_absurd pPrime.right.left)
  | e0 _tail =>
      cases pPrime.left
  | e1 _tail =>
      exact Nat.succ_pos _

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem phiFactorListSumNat_append
    (xs ys : List (List BHist)) :
    phiFactorListSumNat (xs ++ ys) =
      phiFactorListSumNat xs + phiFactorListSumNat ys := by
  induction xs with
  | nil =>
      change phiFactorListSumNat ys = 0 + phiFactorListSumNat ys
      exact (Nat.zero_add (phiFactorListSumNat ys)).symm
  | cons fs fss ih =>
      change eulerPhiFactorsNat fs + phiFactorListSumNat (fss ++ ys) =
        eulerPhiFactorsNat fs + phiFactorListSumNat fss + phiFactorListSumNat ys
      rw [ih]
      exact (Nat.add_assoc (eulerPhiFactorsNat fs)
        (phiFactorListSumNat fss) (phiFactorListSumNat ys)).symm

private theorem list_map_map_local {α β γ : Type}
    (f : α -> β) (g : β -> γ) :
    ∀ xs : List α, (xs.map f).map g = xs.map (fun x => g (f x)) := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons x rest ih =>
      change g (f x) :: (rest.map f).map g =
        g (f x) :: rest.map (fun y => g (f y))
      exact congrArg (fun tail => g (f x) :: tail) ih

private theorem listMem_map_forward_pure {α β : Type} {f : α -> β} :
    ∀ {xs : List α} {y : β},
      y ∈ xs.map f -> ∃ x : α, x ∈ xs ∧ f x = y := by
  intro xs
  induction xs with
  | nil =>
      intro y member
      cases member
  | cons x rest ih =>
      intro y member
      change y ∈ f x :: rest.map f at member
      cases member with
      | head =>
          exact ⟨x, List.Mem.head rest, rfl⟩
      | tail _ tailMember =>
          cases ih tailMember with
          | intro source data =>
              exact ⟨source, List.Mem.tail x data.left, data.right⟩

private theorem listMem_append_forward_pure {α : Type} :
    ∀ {xs ys : List α} {z : α},
      z ∈ xs ++ ys -> z ∈ xs ∨ z ∈ ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys z member
      exact Or.inr member
  | cons x rest ih =>
      intro ys z member
      change z ∈ x :: (rest ++ ys) at member
      cases member with
      | head =>
          exact Or.inl (List.Mem.head rest)
      | tail _ tailMember =>
          cases ih tailMember with
          | inl leftMember =>
              exact Or.inl (List.Mem.tail x leftMember)
          | inr rightMember =>
              exact Or.inr rightMember

private theorem mem_appendFactorListProducts
    {left right : List (List BHist)} {fs : List BHist} :
    fs ∈ appendFactorListProducts left right ->
      ∃ l : List BHist, ∃ r : List BHist,
        l ∈ left ∧ r ∈ right ∧ fs = l ++ r := by
  intro member
  induction right with
  | nil =>
      unfold appendFactorListProducts at member
      exact False.elim (List.not_mem_nil member)
  | cons r rs ih =>
      unfold appendFactorListProducts at member
      have split := listMem_append_forward_pure member
      cases split with
      | inl inHead =>
          have mapped := listMem_map_forward_pure inHead
          cases mapped with
          | intro l lData =>
              exact ⟨l, r, lData.left,
                (show r ∈ r :: rs from List.mem_cons_self), lData.right.symm⟩
      | inr inTail =>
          cases ih inTail with
          | intro l restData =>
              cases restData with
              | intro r' data =>
                  exact ⟨l, r', data.left,
                    List.mem_cons_of_mem r data.right.left, data.right.right⟩

private theorem listContainsPrime_append_false_local {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = false -> listContainsPrime p ys = false ->
        listContainsPrime p (xs ++ ys) = false := by
  intro xs
  induction xs with
  | nil =>
      intro ys _absentLeft absentRight
      exact absentRight
  | cons q qs ih =>
      intro ys absentLeft absentRight
      change (if p = q then true else listContainsPrime p qs) = false at absentLeft
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = false
      by_cases same : p = q
      · rw [if_pos same] at absentLeft
        cases absentLeft
      · rw [if_neg same] at absentLeft
        rw [if_neg same]
        exact ih ys absentLeft absentRight

private theorem primePowerFactorLists_absent_of_ne {p q : BHist} :
    ∀ n : Nat, (p = q -> False) ->
      ∀ fs : List BHist, fs ∈ primePowerFactorLists q n ->
        listContainsPrime p fs = false := by
  intro n
  induction n with
  | zero =>
      intro _ne fs member
      unfold primePowerFactorLists at member
      cases member with
      | head =>
          rfl
      | tail _ tail =>
          exact False.elim (List.not_mem_nil tail)
  | succ n ih =>
      intro ne fs member
      unfold primePowerFactorLists at member
      cases member with
      | head =>
          rfl
      | tail _ tail =>
          have mapped := listMem_map_forward_pure tail
          cases mapped with
          | intro gs gsData =>
              cases gsData.right
              change (if p = q then true else listContainsPrime p gs) = false
              by_cases same : p = q
              · exact False.elim (ne same)
              · rw [if_neg same]
                exact ih ne gs gsData.left

private theorem profileDivisorFactorLists_absent_of_profilePrimes_absent
    {p : BHist} :
    ∀ profile : PrimePowerProfile,
      listContainsPrime p (profilePrimes profile) = false ->
        ∀ rest : List BHist, rest ∈ profileDivisorFactorLists profile ->
          listContainsPrime p rest = false := by
  intro profile
  induction profile with
  | nil =>
      intro _absent rest member
      unfold profileDivisorFactorLists at member
      cases member with
      | head =>
          rfl
      | tail _ tail =>
          exact False.elim (List.not_mem_nil tail)
  | cons e es ih =>
      intro absent rest member
      unfold profilePrimes at absent
      unfold profileDivisorFactorLists at member
      change (if p = e.prime then true else listContainsPrime p (profilePrimes es)) =
        false at absent
      by_cases same : p = e.prime
      · rw [if_pos same] at absent
        cases absent
      · rw [if_neg same] at absent
        cases mem_appendFactorListProducts member with
        | intro left leftData =>
            cases leftData with
            | intro right data =>
                cases data.right.right
                have leftAbsent :
                    listContainsPrime p left = false :=
                  primePowerFactorLists_absent_of_ne e.exponent same left data.left
                have rightAbsent :
                    listContainsPrime p right = false :=
                  ih absent right data.right.left
                exact listContainsPrime_append_false_local left right leftAbsent rightAbsent

private theorem primePowerFactorLists_no_common_of_rest_absent
    (p : BHist) :
    ∀ n : Nat, ∀ fs rest : List BHist,
      fs ∈ primePowerFactorLists p n ->
        listContainsPrime p rest = false -> listNoCommonPrime fs rest := by
  intro n
  induction n with
  | zero =>
      intro fs rest member _absent
      unfold primePowerFactorLists at member
      cases member with
      | head =>
          trivial
      | tail _ tail =>
          exact False.elim (List.not_mem_nil tail)
  | succ n ih =>
      intro fs rest member absent
      unfold primePowerFactorLists at member
      cases member with
      | head =>
          trivial
      | tail _ tail =>
          have mapped := listMem_map_forward_pure tail
          cases mapped with
          | intro base data =>
              cases data.right
              change listNoCommonPrime (p :: base) rest
              exact And.intro absent (ih base rest data.left absent)

private theorem primePowerFactorLists_cons_members_contain
    (p : BHist) :
    ∀ n : Nat, ∀ fs : List BHist,
      fs ∈ (primePowerFactorLists p n).map (fun rest => p :: rest) ->
        listContainsPrime p fs = true := by
  intro n fs member
  have mapped := listMem_map_forward_pure member
  cases mapped with
  | intro rest data =>
      cases data.right
      change (if p = p then true else listContainsPrime p rest) = true
      rw [if_pos rfl]

private theorem phiFactorListSumNat_map_cons_present
    (p : BHist) :
    ∀ xs : List (List BHist),
      (∀ fs : List BHist, fs ∈ xs -> listContainsPrime p fs = true) ->
        phiFactorListSumNat (xs.map (fun fs => p :: fs)) =
          bwordLength p * phiFactorListSumNat xs := by
  intro xs
  induction xs with
  | nil =>
      intro _allPresent
      rfl
  | cons fs fss ih =>
      intro allPresent
      change
        eulerPhiFactorsNat (p :: fs) +
            phiFactorListSumNat (fss.map (fun fs => p :: fs)) =
          bwordLength p *
            (eulerPhiFactorsNat fs + phiFactorListSumNat fss)
      have headPresent : listContainsPrime p fs = true :=
        allPresent fs (show fs ∈ fs :: fss from List.mem_cons_self)
      change
        (if listContainsPrime p fs then bwordLength p * eulerPhiFactorsNat fs
          else (bwordLength p - 1) * eulerPhiFactorsNat fs) +
            phiFactorListSumNat (fss.map (fun fs => p :: fs)) =
          bwordLength p *
            (eulerPhiFactorsNat fs + phiFactorListSumNat fss)
      rw [headPresent]
      have tail :
          phiFactorListSumNat (fss.map (fun fs => p :: fs)) =
            bwordLength p * phiFactorListSumNat fss :=
        ih (fun tail tailMem => allPresent tail (List.mem_cons_of_mem fs tailMem))
      rw [tail]
      exact (Nat.mul_add (bwordLength p)
        (eulerPhiFactorsNat fs) (phiFactorListSumNat fss)).symm

private theorem phiPrimePowerFactorLists_cons_sum
    {p : BHist} (pPrime : NatPrime p) :
    ∀ n : Nat,
      1 + phiFactorListSumNat
        ((primePowerFactorLists p n).map (fun fs => p :: fs)) =
        bwordLength p * phiFactorListSumNat (primePowerFactorLists p n) := by
  intro n
  induction n with
  | zero =>
      change 1 + ((bwordLength p - 1) * 1 + 0) =
        bwordLength p * (1 + 0)
      rw [Nat.mul_one, Nat.add_zero, Nat.add_zero]
      rw [Nat.mul_one]
      exact nat_one_add_pred_of_pos (natPrime_length_pos pPrime)
  | succ n ih =>
      unfold primePowerFactorLists
      change
        1 + ((bwordLength p - 1) * 1 +
          phiFactorListSumNat
            (((primePowerFactorLists p n).map (fun fs => p :: fs)).map
              (fun fs => p :: fs))) =
        bwordLength p *
          (1 + phiFactorListSumNat
            ((primePowerFactorLists p n).map (fun fs => p :: fs)))
      rw [Nat.mul_one]
      rw [phiFactorListSumNat_map_cons_present p
        ((primePowerFactorLists p n).map (fun fs => p :: fs))
        (primePowerFactorLists_cons_members_contain p n)]
      calc
        1 + ((bwordLength p - 1) +
            bwordLength p *
              phiFactorListSumNat
                ((primePowerFactorLists p n).map (fun fs => p :: fs))) =
          (1 + (bwordLength p - 1)) +
            bwordLength p *
              phiFactorListSumNat
                ((primePowerFactorLists p n).map (fun fs => p :: fs)) := by
            exact (Nat.add_assoc 1 (bwordLength p - 1)
              (bwordLength p *
                phiFactorListSumNat
                  ((primePowerFactorLists p n).map (fun fs => p :: fs)))).symm
        _ = bwordLength p +
            bwordLength p *
              phiFactorListSumNat
                ((primePowerFactorLists p n).map (fun fs => p :: fs)) := by
            rw [nat_one_add_pred_of_pos (natPrime_length_pos pPrime)]
        _ = bwordLength p *
            (1 + phiFactorListSumNat
              ((primePowerFactorLists p n).map (fun fs => p :: fs))) := by
            rw [Nat.mul_add, Nat.mul_one]

private theorem phiPrimePowerFactorLists_sum_eq_pow
    {p : BHist} (pPrime : NatPrime p) :
    ∀ n : Nat,
      phiFactorListSumNat (primePowerFactorLists p n) =
        natPow (bwordLength p) n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold primePowerFactorLists
      change
        1 + phiFactorListSumNat
          ((primePowerFactorLists p n).map (fun fs => p :: fs)) =
        bwordLength p * natPow (bwordLength p) n
      rw [phiPrimePowerFactorLists_cons_sum pPrime n]
      rw [ih]

private theorem phiFactorListSumNat_map_append_right :
    ∀ (left : List (List BHist)) (rest : List BHist),
      (∀ l : List BHist, l ∈ left -> listNoCommonPrime l rest) ->
        phiFactorListSumNat (left.map (fun l => l ++ rest)) =
          phiFactorListSumNat left * eulerPhiFactorsNat rest
  | [], rest, _disjoint => by
      change 0 = 0 * eulerPhiFactorsNat rest
      exact (Nat.zero_mul (eulerPhiFactorsNat rest)).symm
  | l :: ls, rest, disjoint => by
      change
        eulerPhiFactorsNat (l ++ rest) +
            phiFactorListSumNat (ls.map (fun l => l ++ rest)) =
          (eulerPhiFactorsNat l + phiFactorListSumNat ls) *
            eulerPhiFactorsNat rest
      have headDisjoint : listNoCommonPrime l rest :=
        disjoint l (show l ∈ l :: ls from List.mem_cons_self)
      have headValue :
          eulerPhiFactorsNat (l ++ rest) =
            eulerPhiFactorsNat l * eulerPhiFactorsNat rest :=
        eulerPhiFactorsNat_append_disjoint l rest headDisjoint
      have tailValue :
          phiFactorListSumNat (ls.map (fun l => l ++ rest)) =
            phiFactorListSumNat ls * eulerPhiFactorsNat rest :=
        phiFactorListSumNat_map_append_right ls rest
          (fun tail tailMem => disjoint tail (List.mem_cons_of_mem l tailMem))
      calc
        eulerPhiFactorsNat (l ++ rest) +
            phiFactorListSumNat (ls.map (fun l => l ++ rest)) =
          eulerPhiFactorsNat l * eulerPhiFactorsNat rest +
            phiFactorListSumNat ls * eulerPhiFactorsNat rest := by
            exact nat_add_congr_pure headValue tailValue
        _ =
          (eulerPhiFactorsNat l + phiFactorListSumNat ls) *
            eulerPhiFactorsNat rest := by
            exact (nat_add_mul_pure (eulerPhiFactorsNat l)
              (phiFactorListSumNat ls) (eulerPhiFactorsNat rest)).symm

private theorem phiFactorListSumNat_appendFactorListProducts_mul :
    ∀ (left right : List (List BHist)),
      (∀ l : List BHist, l ∈ left ->
        ∀ r : List BHist, r ∈ right -> listNoCommonPrime l r) ->
        phiFactorListSumNat (appendFactorListProducts left right) =
          phiFactorListSumNat left * phiFactorListSumNat right
  | left, [], _disjoint => by
      rfl
  | left, rest :: rests, disjoint => by
      unfold appendFactorListProducts
      have split :
          phiFactorListSumNat
              (left.map (fun l => l ++ rest) ++
                appendFactorListProducts left rests) =
            phiFactorListSumNat (left.map (fun l => l ++ rest)) +
              phiFactorListSumNat (appendFactorListProducts left rests) :=
        phiFactorListSumNat_append
          (left.map (fun l => l ++ rest)) (appendFactorListProducts left rests)
      have head :
          phiFactorListSumNat (left.map (fun l => l ++ rest)) =
            phiFactorListSumNat left * eulerPhiFactorsNat rest :=
        phiFactorListSumNat_map_append_right left rest
          (fun l lMem => disjoint l lMem rest
            (show rest ∈ rest :: rests from List.mem_cons_self))
      have tail :
          phiFactorListSumNat (appendFactorListProducts left rests) =
            phiFactorListSumNat left * phiFactorListSumNat rests :=
        phiFactorListSumNat_appendFactorListProducts_mul left rests
          (fun l lMem r rMem => disjoint l lMem r
            (List.mem_cons_of_mem rest rMem))
      calc
        phiFactorListSumNat
            (left.map (fun l => l ++ rest) ++
              appendFactorListProducts left rests) =
          phiFactorListSumNat (left.map (fun l => l ++ rest)) +
            phiFactorListSumNat (appendFactorListProducts left rests) := split
        _ =
          phiFactorListSumNat left * eulerPhiFactorsNat rest +
            phiFactorListSumNat left * phiFactorListSumNat rests := by
            exact nat_add_congr_pure head tail
        _ =
          phiFactorListSumNat left *
            (eulerPhiFactorsNat rest + phiFactorListSumNat rests) := by
            exact (Nat.mul_add (phiFactorListSumNat left)
              (eulerPhiFactorsNat rest) (phiFactorListSumNat rests)).symm

private theorem profilePhiDivisorSumNat_eq_productNat
    {profile : PrimePowerProfile} :
    ProfileValid profile ->
      profilePhiDivisorSumNat profile = profileProductNat profile := by
  intro valid
  induction valid with
  | nil =>
      rfl
  | cons pPrime _nonzero absentTail validTail ih =>
      change
        phiFactorListSumNat
          (appendFactorListProducts
            (primePowerFactorLists _ _)
            (profileDivisorFactorLists _)) =
          natPow (bwordLength _) _ * profileProductNat _
      rw [phiFactorListSumNat_appendFactorListProducts_mul]
      · rw [phiPrimePowerFactorLists_sum_eq_pow pPrime]
        unfold profilePhiDivisorSumNat at ih
        rw [ih]
      · intro l lMem rest restMem
        have restAbsent :
            listContainsPrime _ rest = false :=
          profileDivisorFactorLists_absent_of_profilePrimes_absent
            _ absentTail rest restMem
        exact primePowerFactorLists_no_common_of_rest_absent _ _ l rest lMem restAbsent

private theorem primeFlatProductNat_append
    (xs ys : List BHist) :
    primeFlatProductNat (xs ++ ys) =
      primeFlatProductNat xs * primeFlatProductNat ys := by
  induction xs with
  | nil =>
      change primeFlatProductNat ys = 1 * primeFlatProductNat ys
      rw [Nat.one_mul]
  | cons x xs ih =>
      change bwordLength x * primeFlatProductNat (xs ++ ys) =
        (bwordLength x * primeFlatProductNat xs) * primeFlatProductNat ys
      rw [ih]
      exact (nat_mul_assoc_pure (bwordLength x)
        (primeFlatProductNat xs) (primeFlatProductNat ys)).symm

private theorem primeFlatProductNat_expandPrimePower
    (p : BHist) :
    ∀ n : Nat,
      primeFlatProductNat (expandPrimePower p n) =
        natPow (bwordLength p) n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change bwordLength p * primeFlatProductNat (expandPrimePower p n) =
        bwordLength p * natPow (bwordLength p) n
      rw [ih]

private theorem primeFlatProductNat_expandProfile
    (profile : PrimePowerProfile) :
    primeFlatProductNat (expandProfile profile) =
      profileProductNat profile := by
  induction profile with
  | nil =>
      rfl
  | cons e es ih =>
      change primeFlatProductNat (expandPrimePower e.prime e.exponent ++ expandProfile es) =
        natPow (bwordLength e.prime) e.exponent * profileProductNat es
      rw [primeFlatProductNat_append]
      rw [primeFlatProductNat_expandPrimePower]
      rw [ih]

private theorem PrimeFactorizationProduct_length_eq_flat
    {entries : List BHist} {n : BHist} :
    PrimeFactorizationProduct entries n ->
      bwordLength n = primeFlatProductNat entries := by
  intro product
  induction entries generalizing n with
  | nil =>
      unfold primeFlatProductNat
      cases product
      rfl
  | cons p ps ih =>
      cases product with
      | intro _pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold primeFlatProductNat
              rw [NatMul_bwordLength tailData.right]
              exact congrArg (fun t => bwordLength p * t) (ih tailData.left)

theorem profilePhiDivisorSum_unary (profile : PrimePowerProfile) :
    UnaryHistory (profilePhiDivisorSum profile) := by
  unfold profilePhiDivisorSum
  exact natToUnary_unary _

theorem gauss_phi_divisor_sum_nat_of_profile
    {profile : PrimePowerProfile} :
    ProfileValid profile ->
      profilePhiDivisorSumNat profile = profileProductNat profile :=
  profilePhiDivisorSumNat_eq_productNat

theorem gauss_phi_divisor_sum_of_factorization
    {n : BHist} {profile : PrimePowerProfile} :
    ProfileValid profile ->
      PrimeFactorizationProduct (expandProfile profile) n ->
        hsame (profilePhiDivisorSum profile) n := by
  intro valid product
  apply unary_hsame_of_length
  · exact profilePhiDivisorSum_unary profile
  · exact PrimeFactorizationProduct_result_unary product
  · unfold profilePhiDivisorSum
    rw [natToUnary_length]
    rw [profilePhiDivisorSumNat_eq_productNat valid]
    rw [← primeFlatProductNat_expandProfile profile]
    exact (PrimeFactorizationProduct_length_eq_flat product).symm

theorem gauss_phi_divisor_sum_of_prime_factorization
    {n : BHist} {profile : PrimePowerProfile} :
    DivisorCountOfProfile n (divisorCountProfile profile) profile ->
      hsame (profilePhiDivisorSum profile) n := by
  intro profileData
  exact gauss_phi_divisor_sum_of_factorization
    profileData.left profileData.right.left.right

end BEDC.Derived.PhiDivisorSum
