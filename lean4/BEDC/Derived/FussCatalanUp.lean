import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp
import BEDC.Derived.IntUp

namespace BEDC.Derived.FussCatalanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def fussCatalanPromptDenom (m n : Nat) : Nat :=
  m * n + 1

def fussCatalanPromptNumerator (m n : Nat) : Nat :=
  C (m * n + n) n

def fussCatalanPromptCount (m n : Nat) : Nat :=
  fussCatalanPromptNumerator m n / fussCatalanPromptDenom m n

def fussCatalanDenom (m n : Nat) : Nat :=
  (m - 1) * n + 1

def fussCatalanNumerator (m n : Nat) : Nat :=
  C (m * n) n

def fussCatalanCount (m n : Nat) : Nat :=
  fussCatalanNumerator m n / fussCatalanDenom m n

def fussCatalanFn (m n : BHist) : BHist :=
  natToUnary (fussCatalanCount (bwordLength m) (bwordLength n))

def fussCatalanExactDivision (m n q : Nat) : Prop :=
  q * fussCatalanDenom m n = fussCatalanNumerator m n

def natRange : Nat -> List Nat
  | 0 => [0]
  | Nat.succ n => natRange n ++ [Nat.succ n]

def listNatSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

def listNatProduct : List Nat -> Nat
  | [] => 1
  | x :: xs => x * listNatProduct xs

def listAppend {A : Type u} : List A -> List A -> List A
  | [], ys => ys
  | x :: xs, ys => x :: listAppend xs ys

def listBindNat (xs : List Nat) (f : Nat -> List (List Nat)) : List (List Nat) :=
  match xs with
  | [] => []
  | x :: tail => listAppend (f x) (listBindNat tail f)

def natCompositions : Nat -> Nat -> List (List Nat)
  | 0, 0 => [[]]
  | 0, Nat.succ _ => []
  | Nat.succ slots, total =>
      listBindNat (natRange total)
        (fun head =>
          (natCompositions slots (total - head)).map
            (fun tail => head :: tail))

def treeFussCatalanFuel (m : Nat) : Nat -> Nat -> Nat
  | 0, _ => 1
  | Nat.succ _n, 0 => 0
  | Nat.succ n, Nat.succ fuel =>
      listNatSum
        ((natCompositions m n).map
          (fun parts =>
            listNatProduct
              (parts.map (fun k => treeFussCatalanFuel m k fuel))))

def treeFussCatalanCount (m n : Nat) : Nat :=
  treeFussCatalanFuel m n n

theorem fussCatalanPrompt_shift (m n : Nat) :
    fussCatalanPromptCount m n = fussCatalanCount (Nat.succ m) n := by
  unfold fussCatalanPromptCount fussCatalanCount
  unfold fussCatalanPromptNumerator fussCatalanNumerator
  unfold fussCatalanPromptDenom fussCatalanDenom
  rw [Nat.succ_mul]
  rfl

theorem fussCatalanFn_unary_result (m n : BHist) :
    UnaryHistory (fussCatalanFn m n) := by
  unfold fussCatalanFn
  exact natToUnary_unary _

theorem treeFussCatalanFuel_zero (m fuel : Nat) :
    treeFussCatalanFuel m 0 fuel = 1 := by
  cases fuel <;> rfl

theorem treeFussCatalanFuel_succ (m n fuel : Nat) :
    treeFussCatalanFuel m (Nat.succ n) (Nat.succ fuel) =
      listNatSum
        ((natCompositions m n).map
          (fun parts =>
            listNatProduct
              (parts.map (fun k => treeFussCatalanFuel m k fuel)))) := by
  rfl

abbrev BinaryFussCatalan : BHist -> BHist -> Prop :=
  BEDC.Derived.CatalanUp.Catalan

abbrev BinaryFussCatalanConv : BHist -> BHist -> BHist -> Prop :=
  BEDC.Derived.CatalanUp.CatalanConv

theorem binaryFussCatalan_to_catalan {n value : BHist} :
    BinaryFussCatalan n value ->
      BEDC.Derived.CatalanUp.Catalan n value := by
  intro cat
  exact cat

theorem catalan_to_binaryFussCatalan {n value : BHist} :
    BEDC.Derived.CatalanUp.Catalan n value ->
      BinaryFussCatalan n value := by
  intro cat
  exact cat

theorem binaryFussCatalan_iff_catalan {n value : BHist} :
    BinaryFussCatalan n value <->
      BEDC.Derived.CatalanUp.Catalan n value := by
  constructor
  · intro cat
    exact binaryFussCatalan_to_catalan cat
  · intro cat
    exact catalan_to_binaryFussCatalan cat

theorem binaryFussCatalan_zero :
    BinaryFussCatalan BHist.Empty (natToUnary 1) :=
  BEDC.Derived.CatalanUp.catalan_zero

theorem binaryFussCatalan_one :
    BinaryFussCatalan (natToUnary 1) (natToUnary 1) :=
  catalan_to_binaryFussCatalan BEDC.Derived.CatalanUp.catalan_one

theorem binaryFussCatalan_two :
    BinaryFussCatalan (natToUnary 2) (natToUnary 2) :=
  catalan_to_binaryFussCatalan BEDC.Derived.CatalanUp.catalan_two

theorem binaryFussCatalan_three :
    BinaryFussCatalan (natToUnary 3) (natToUnary 5) :=
  catalan_to_binaryFussCatalan BEDC.Derived.CatalanUp.catalan_three

theorem fussCatalan_binary_closed_zero :
    fussCatalanCount 2 0 = 1 := by
  rfl

theorem fussCatalan_binary_closed_one :
    fussCatalanCount 2 1 = 1 := by
  rfl

theorem fussCatalan_binary_closed_two :
    fussCatalanCount 2 2 = 2 := by
  rfl

theorem fussCatalan_binary_closed_three :
    fussCatalanCount 2 3 = 5 := by
  rfl

theorem fussCatalan_binary_exact_zero :
    fussCatalanExactDivision 2 0 (fussCatalanCount 2 0) := by
  rfl

theorem fussCatalan_binary_exact_one :
    fussCatalanExactDivision 2 1 (fussCatalanCount 2 1) := by
  rfl

theorem fussCatalan_binary_exact_two :
    fussCatalanExactDivision 2 2 (fussCatalanCount 2 2) := by
  rfl

theorem fussCatalan_binary_exact_three :
    fussCatalanExactDivision 2 3 (fussCatalanCount 2 3) := by
  rfl

theorem treeFussCatalan_binary_closed_zero :
    treeFussCatalanCount 2 0 = 1 := by
  rfl

theorem treeFussCatalan_binary_closed_one :
    treeFussCatalanCount 2 1 = 1 := by
  rfl

theorem treeFussCatalan_binary_closed_two :
    treeFussCatalanCount 2 2 = 2 := by
  rfl

theorem treeFussCatalan_binary_closed_three :
    treeFussCatalanCount 2 3 = 5 := by
  rfl

theorem binaryFussCatalan_small_values :
    BinaryFussCatalan BHist.Empty (natToUnary 1) ∧
      BinaryFussCatalan (natToUnary 1) (natToUnary 1) ∧
        BinaryFussCatalan (natToUnary 2) (natToUnary 2) ∧
          BinaryFussCatalan (natToUnary 3) (natToUnary 5) := by
  constructor
  · exact binaryFussCatalan_zero
  · constructor
    · exact binaryFussCatalan_one
    · constructor
      · exact binaryFussCatalan_two
      · exact binaryFussCatalan_three

theorem FussCatalanUp_constructive_export :
    (∀ m n : Nat,
      fussCatalanPromptCount m n = fussCatalanCount (Nat.succ m) n) ∧
      (∀ m fuel : Nat, treeFussCatalanFuel m 0 fuel = 1) ∧
      (∀ m n fuel : Nat,
        treeFussCatalanFuel m (Nat.succ n) (Nat.succ fuel) =
          listNatSum
            ((natCompositions m n).map
              (fun parts =>
                listNatProduct
                  (parts.map (fun k => treeFussCatalanFuel m k fuel))))) ∧
      (∀ {n value : BHist},
        BinaryFussCatalan n value <->
          BEDC.Derived.CatalanUp.Catalan n value) ∧
      fussCatalanCount 2 0 = 1 ∧ fussCatalanCount 2 1 = 1 ∧
        fussCatalanCount 2 2 = 2 ∧ fussCatalanCount 2 3 = 5 ∧
          fussCatalanExactDivision 2 0 (fussCatalanCount 2 0) ∧
            fussCatalanExactDivision 2 1 (fussCatalanCount 2 1) ∧
              fussCatalanExactDivision 2 2 (fussCatalanCount 2 2) ∧
                fussCatalanExactDivision 2 3 (fussCatalanCount 2 3) := by
  constructor
  · intro m n
    exact fussCatalanPrompt_shift m n
  · constructor
    · intro m fuel
      exact treeFussCatalanFuel_zero m fuel
    · constructor
      · intro m n fuel
        exact treeFussCatalanFuel_succ m n fuel
      · constructor
        · intro n value
          exact binaryFussCatalan_iff_catalan
        · constructor
          · exact fussCatalan_binary_closed_zero
          · constructor
            · exact fussCatalan_binary_closed_one
            · constructor
              · exact fussCatalan_binary_closed_two
              · constructor
                · exact fussCatalan_binary_closed_three
                · constructor
                  · exact fussCatalan_binary_exact_zero
                  · constructor
                    · exact fussCatalan_binary_exact_one
                    · constructor
                      · exact fussCatalan_binary_exact_two
                      · exact fussCatalan_binary_exact_three

end BEDC.Derived.FussCatalanUp
