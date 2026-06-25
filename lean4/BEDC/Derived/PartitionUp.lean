import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.NatUp.NatAdd
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.PartitionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty
abbrev UnaryTwo : BHist := BHist.e1 UnaryOne
abbrev UnaryThree : BHist := BHist.e1 UnaryTwo
abbrev UnaryFour : BHist := BHist.e1 UnaryThree
abbrev UnaryFive : BHist := BHist.e1 UnaryFour
abbrev UnarySix : BHist := BHist.e1 UnaryFive
abbrev UnarySeven : BHist := BHist.e1 UnarySix

def partitionRowZero : Nat -> Nat := fun _ => 1

def previousPartitionRow : List (Nat -> Nat) -> Nat -> Nat -> Nat
  | [], _, _ => 0
  | row :: _, 0, k => row k
  | _ :: rows, Nat.succ idx, k => previousPartitionRow rows idx k

-- 第 `current` 行由前面所有行构造: 第一项是零, 后续项按最大部件递推。
def partitionRowFromPrevious (current : Nat) (rows : List (Nat -> Nat)) : Nat -> Nat
  | 0 => 0
  | Nat.succ k =>
      partitionRowFromPrevious current rows k +
        if Nat.succ k <= current then
          previousPartitionRow rows k (Nat.succ k)
        else 0

def partitionRows : Nat -> List (Nat -> Nat)
  | 0 => [partitionRowZero]
  | Nat.succ n => partitionRowFromPrevious (Nat.succ n) (partitionRows n) :: partitionRows n

-- 受限分拆数: `restrictedPartition n k` 只允许最大部件不超过 `k`。
def restrictedPartition (n k : Nat) : Nat :=
  previousPartitionRow (partitionRows n) 0 k

def partitionNumber (n : Nat) : Nat :=
  restrictedPartition n n

def restrictedPartitionUp (n k : BHist) : BHist :=
  natToUnary (restrictedPartition (bwordLength n) (bwordLength k))

def partitionNumberUp (n : BHist) : BHist :=
  natToUnary (partitionNumber (bwordLength n))

theorem restrictedPartition_zero_left (k : Nat) :
    restrictedPartition 0 k = 1 := by
  rfl

theorem restrictedPartition_positive_zero (n : Nat) :
    restrictedPartition (Nat.succ n) 0 = 0 := by
  rfl

theorem previousPartitionRow_partitionRows_le :
    ∀ n idx t : Nat, idx <= n ->
      previousPartitionRow (partitionRows n) idx t = restrictedPartition (n - idx) t := by
  intro n
  induction n with
  | zero =>
      intro idx t h
      cases idx with
      | zero =>
          rfl
      | succ idx =>
          cases h
  | succ n ih =>
      intro idx t h
      cases idx with
      | zero =>
          rfl
      | succ idx =>
          change previousPartitionRow (partitionRows n) idx t =
            restrictedPartition (Nat.succ n - Nat.succ idx) t
          rw [Nat.succ_sub_succ_eq_sub]
          exact ih idx t (Nat.succ_le_succ_iff.mp h)

theorem partitionRowFromPrevious_succ (current rows k) :
    partitionRowFromPrevious current rows (Nat.succ k) =
      partitionRowFromPrevious current rows k +
        if Nat.succ k <= current then previousPartitionRow rows k (Nat.succ k) else 0 := by
  rfl

theorem restrictedPartition_recurrence (n k : Nat) :
    restrictedPartition (Nat.succ n) (Nat.succ k) =
      restrictedPartition (Nat.succ n) k +
        if Nat.succ k <= Nat.succ n then
          restrictedPartition ((Nat.succ n) - (Nat.succ k)) (Nat.succ k)
        else 0 := by
  unfold restrictedPartition
  change partitionRowFromPrevious (Nat.succ n) (partitionRows n) (Nat.succ k) =
    partitionRowFromPrevious (Nat.succ n) (partitionRows n) k +
      if Nat.succ k <= Nat.succ n then
        previousPartitionRow (partitionRows (Nat.succ n - Nat.succ k)) 0 (Nat.succ k)
      else 0
  rw [partitionRowFromPrevious_succ]
  split
  · rename_i h
    rw [previousPartitionRow_partitionRows_le n k (Nat.succ k)
      (Nat.succ_le_succ_iff.mp h)]
    rw [Nat.succ_sub_succ_eq_sub]
    unfold restrictedPartition
    rfl
  · rfl

theorem restrictedPartition_guarded_recurrence_inside (n k : Nat)
    (h : Nat.succ k <= Nat.succ n) :
    restrictedPartition (Nat.succ n) (Nat.succ k) =
      restrictedPartition (Nat.succ n) k +
        restrictedPartition ((Nat.succ n) - (Nat.succ k)) (Nat.succ k) := by
  rw [restrictedPartition_recurrence, if_pos h]

theorem partitionNumber_definition (n : Nat) :
    partitionNumber n = restrictedPartition n n := by
  rfl

theorem restrictedPartitionUp_unary_result (n k : BHist) :
    UnaryHistory (restrictedPartitionUp n k) := by
  unfold restrictedPartitionUp
  exact natToUnary_unary _

theorem partitionNumberUp_unary_result (n : BHist) :
    UnaryHistory (partitionNumberUp n) := by
  unfold partitionNumberUp
  exact natToUnary_unary _

theorem natToUnary_append (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

theorem restrictedPartitionUp_zero_left (k : Nat) :
    restrictedPartitionUp BHist.Empty (natToUnary k) = UnaryOne := by
  unfold restrictedPartitionUp
  rw [NatUp_unary_standard_bridge.left]
  rw [natToUnary_length]
  rfl

theorem restrictedPartitionUp_positive_zero (n : Nat) :
    restrictedPartitionUp (natToUnary (Nat.succ n)) BHist.Empty = BHist.Empty := by
  unfold restrictedPartitionUp
  rw [natToUnary_length]
  rw [NatUp_unary_standard_bridge.left]
  rfl

theorem restrictedPartitionUp_recurrence_natToUnary (n k : Nat) :
    restrictedPartitionUp (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (restrictedPartition (Nat.succ n) k +
          if Nat.succ k <= Nat.succ n then
            restrictedPartition ((Nat.succ n) - (Nat.succ k)) (Nat.succ k)
          else 0) := by
  unfold restrictedPartitionUp
  rw [natToUnary_length, natToUnary_length]
  exact congrArg natToUnary (restrictedPartition_recurrence n k)

theorem restrictedPartitionUp_guarded_recurrence_natToUnary (n k : Nat)
    (h : Nat.succ k <= Nat.succ n) :
    restrictedPartitionUp (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        (restrictedPartition (Nat.succ n) k +
          restrictedPartition ((Nat.succ n) - (Nat.succ k)) (Nat.succ k)) := by
  rw [restrictedPartitionUp_recurrence_natToUnary, if_pos h]

theorem partitionNumber_zero :
    partitionNumber 0 = 1 := by
  rfl

theorem partitionNumber_one :
    partitionNumber 1 = 1 := by
  rfl

theorem partitionNumber_two :
    partitionNumber 2 = 2 := by
  rfl

theorem partitionNumber_three :
    partitionNumber 3 = 3 := by
  rfl

theorem partitionNumber_four :
    partitionNumber 4 = 5 := by
  rfl

theorem partitionNumber_five :
    partitionNumber 5 = 7 := by
  rfl

theorem partitionNumberUp_zero :
    partitionNumberUp BHist.Empty = UnaryOne := by
  unfold partitionNumberUp
  rw [NatUp_unary_standard_bridge.left]
  rfl

theorem partitionNumberUp_one :
    partitionNumberUp UnaryOne = UnaryOne := by
  unfold partitionNumberUp
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
  rw [NatUp_unary_standard_bridge.left]
  rw [partitionNumber_one]
  rfl

theorem partitionNumberUp_two :
    partitionNumberUp UnaryTwo = UnaryTwo := by
  unfold partitionNumberUp
  rw [NatUp_unary_standard_bridge.right.left UnaryOne
    (unary_e1_closed unary_empty)]
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
  rw [NatUp_unary_standard_bridge.left]
  rw [partitionNumber_two]
  rfl

theorem partitionNumberUp_three :
    partitionNumberUp UnaryThree = UnaryThree := by
  unfold partitionNumberUp
  rw [NatUp_unary_standard_bridge.right.left UnaryTwo
    (unary_e1_closed (unary_e1_closed unary_empty))]
  rw [NatUp_unary_standard_bridge.right.left UnaryOne
    (unary_e1_closed unary_empty)]
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
  rw [NatUp_unary_standard_bridge.left]
  rw [partitionNumber_three]
  rfl

theorem partitionNumberUp_four :
    partitionNumberUp UnaryFour = UnaryFive := by
  unfold partitionNumberUp
  rw [NatUp_unary_standard_bridge.right.left UnaryThree
    (unary_e1_closed (unary_e1_closed (unary_e1_closed unary_empty)))]
  rw [NatUp_unary_standard_bridge.right.left UnaryTwo
    (unary_e1_closed (unary_e1_closed unary_empty))]
  rw [NatUp_unary_standard_bridge.right.left UnaryOne
    (unary_e1_closed unary_empty)]
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
  rw [NatUp_unary_standard_bridge.left]
  rw [partitionNumber_four]
  rfl

theorem partitionNumberUp_five :
    partitionNumberUp UnaryFive = UnarySeven := by
  unfold partitionNumberUp
  rw [NatUp_unary_standard_bridge.right.left UnaryFour
    (unary_e1_closed
      (unary_e1_closed (unary_e1_closed (unary_e1_closed unary_empty))))]
  rw [NatUp_unary_standard_bridge.right.left UnaryThree
    (unary_e1_closed (unary_e1_closed (unary_e1_closed unary_empty)))]
  rw [NatUp_unary_standard_bridge.right.left UnaryTwo
    (unary_e1_closed (unary_e1_closed unary_empty))]
  rw [NatUp_unary_standard_bridge.right.left UnaryOne
    (unary_e1_closed unary_empty)]
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
  rw [NatUp_unary_standard_bridge.left]
  rw [partitionNumber_five]
  rfl

theorem restrictedPartition_add_step_natToUnary (n k : Nat)
    (h : Nat.succ k <= Nat.succ n) :
    NatAdd
      (natToUnary (restrictedPartition (Nat.succ n) k))
      (natToUnary (restrictedPartition ((Nat.succ n) - (Nat.succ k)) (Nat.succ k)))
      (natToUnary (restrictedPartition (Nat.succ n) (Nat.succ k))) := by
  rw [restrictedPartition_guarded_recurrence_inside n k h]
  exact
    ⟨natToUnary_unary _, natToUnary_unary _,
      cont_intro (natToUnary_append _ _).symm⟩

theorem partitionIntegerRelCommRing_zero_add_one :
    BEDC.Algebra.Rel.IntEq
      (BEDC.Algebra.Rel.IntegerUp_RelCommRing.add
        BEDC.Algebra.Rel.intZero BEDC.Algebra.Rel.intOne)
      BEDC.Algebra.Rel.intOne :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing.zero_add BEDC.Algebra.Rel.intOne

theorem partitionFiniteFold_integer_empty_sum :
    BEDC.Algebra.Rel.IntEq
      (BEDC.Algebra.FiniteFold.listSum
        BEDC.Algebra.Rel.IntegerUp_RelCommRing [])
      BEDC.Algebra.Rel.intZero :=
  BEDC.Algebra.FiniteFold.sum_nil BEDC.Algebra.Rel.IntegerUp_RelCommRing

theorem PartitionUp_constructive_export :
    partitionNumber 0 = 1 ∧
      partitionNumber 1 = 1 ∧
      partitionNumber 2 = 2 ∧
      partitionNumber 3 = 3 ∧
      partitionNumber 4 = 5 ∧
      partitionNumber 5 = 7 := by
  constructor
  · exact partitionNumber_zero
  · constructor
    · exact partitionNumber_one
    · constructor
      · exact partitionNumber_two
      · constructor
        · exact partitionNumber_three
        · constructor
          · exact partitionNumber_four
          · exact partitionNumber_five

def PartitionBHistCarrier [AskSetup] [PackageSetup]
    (listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory listRow ∧ UnaryHistory partRows ∧ UnaryHistory sumRow ∧
    UnaryHistory decreaseRows ∧ UnaryHistory boundary ∧ Cont listRow sumRow route ∧
      Cont decreaseRows boundary provenance ∧ Cont route provenance endpoint ∧
        PkgSig bundle endpoint pkg

def PartitionYoungLedgerClassifier [AskSetup] [PackageSetup]
    (listRow partRows sumRow decreaseRows boundary route provenance endpoint listRow' partRows'
      sumRow' decreaseRows' boundary' route' provenance' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance endpoint
      bundle pkg ∧
    hsame listRow listRow' ∧ hsame partRows partRows' ∧ hsame sumRow sumRow' ∧
      hsame decreaseRows decreaseRows' ∧ hsame boundary boundary' ∧
        Cont listRow' sumRow' route' ∧ Cont decreaseRows' boundary' provenance' ∧
          Cont route' provenance' endpoint'

theorem PartitionBHistCarrier_obligation [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      UnaryHistory listRow ∧ UnaryHistory partRows ∧ UnaryHistory sumRow ∧
        UnaryHistory decreaseRows ∧ UnaryHistory boundary ∧ Cont listRow sumRow route ∧
          Cont decreaseRows boundary provenance ∧ Cont route provenance endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

theorem PartitionBHistCarrier_finite_namecert_surface [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧
        PkgSig bundle endpoint pkg := by
  intro carrier
  have endpointSource :
      PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
          endpoint bundle pkg ∧
        hsame endpoint endpoint :=
    And.intro carrier (hsame_refl endpoint)
  have core :
      NameCert
        (fun row : BHist =>
          PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
            endpoint bundle pkg ∧ hsame row endpoint)
        hsame := {
    carrier_inhabited := Exists.intro endpoint endpointSource
    equiv_refl := by
      intro h _source
      exact hsame_refl h
    equiv_symm := by
      intro _h _k same
      exact hsame_symm same
    equiv_trans := by
      intro _h _k _r sameHK sameKR
      exact hsame_trans sameHK sameKR
    carrier_respects_equiv := by
      intro h k sameHK sourceH
      exact And.intro sourceH.left (hsame_trans (hsame_symm sameHK) sourceH.right)
  }
  exact
    And.intro
      {
        core := core
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }
      carrier.right.right.right.right.right.right.right.right

theorem PartitionBHistCarrier_classifier_stability [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint listRow' partRows'
      sumRow' decreaseRows' boundary' route' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      hsame listRow listRow' ->
        hsame partRows partRows' ->
          hsame sumRow sumRow' ->
            hsame decreaseRows decreaseRows' ->
              hsame boundary boundary' ->
                Cont listRow' sumRow' route' ->
                  Cont decreaseRows' boundary' provenance' ->
                    Cont route' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        PartitionBHistCarrier listRow' partRows' sumRow' decreaseRows'
                            boundary' route' provenance' endpoint' bundle pkg ∧
                          hsame route route' ∧ hsame provenance provenance' ∧
                            hsame endpoint endpoint' := by
  intro carrier sameList sameParts sameSum sameDecrease sameBoundary routeCont'
    provenanceCont' endpointCont' endpointPkg'
  have routeSame : hsame route route' :=
    cont_respects_hsame sameList sameSum carrier.right.right.right.right.right.left routeCont'
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame sameDecrease sameBoundary
      carrier.right.right.right.right.right.right.left provenanceCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame routeSame provenanceSame
      carrier.right.right.right.right.right.right.right.left endpointCont'
  have transportedCarrier :
      PartitionBHistCarrier listRow' partRows' sumRow' decreaseRows' boundary' route'
        provenance' endpoint' bundle pkg :=
    And.intro (unary_transport carrier.left sameList)
      (And.intro (unary_transport carrier.right.left sameParts)
        (And.intro (unary_transport carrier.right.right.left sameSum)
          (And.intro (unary_transport carrier.right.right.right.left sameDecrease)
            (And.intro (unary_transport carrier.right.right.right.right.left sameBoundary)
              (And.intro routeCont'
                (And.intro provenanceCont' (And.intro endpointCont' endpointPkg')))))))
  exact
    And.intro transportedCarrier
      (And.intro routeSame (And.intro provenanceSame endpointSame))

theorem PartitionYoungLedgerClassifier_transport [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint listRow' partRows'
      sumRow' decreaseRows' boundary' route' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionYoungLedgerClassifier listRow partRows sumRow decreaseRows boundary route
        provenance endpoint listRow' partRows' sumRow' decreaseRows' boundary' route'
        provenance' endpoint' bundle pkg ->
      PkgSig bundle endpoint' pkg ->
        PartitionBHistCarrier listRow' partRows' sumRow' decreaseRows' boundary' route'
            provenance' endpoint' bundle pkg ∧
          hsame route route' ∧ hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro classifier endpointPkg'
  exact
    PartitionBHistCarrier_classifier_stability classifier.left classifier.right.left
      classifier.right.right.left classifier.right.right.right.left
      classifier.right.right.right.right.left classifier.right.right.right.right.right.left
      classifier.right.right.right.right.right.right.left
      classifier.right.right.right.right.right.right.right.left
      classifier.right.right.right.right.right.right.right.right endpointPkg'

theorem PartitionBHistCarrier_young_boundary_package [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint routeBoundary
      packaged : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      Cont route boundary routeBoundary ->
        Cont provenance routeBoundary packaged ->
          PkgSig bundle packaged pkg ->
            UnaryHistory routeBoundary ∧ UnaryHistory packaged ∧
              hsame routeBoundary (append route boundary) ∧
                hsame packaged (append provenance routeBoundary) := by
  intro carrier routeBoundaryCont packagedCont _packagedPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed carrier.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed carrier.right.right.right.left carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have routeBoundaryUnary : UnaryHistory routeBoundary :=
    unary_cont_closed routeUnary carrier.right.right.right.right.left routeBoundaryCont
  have packagedUnary : UnaryHistory packaged :=
    unary_cont_closed provenanceUnary routeBoundaryUnary packagedCont
  exact
    ⟨routeBoundaryUnary,
      packagedUnary,
      routeBoundaryCont,
      packagedCont⟩

theorem PartitionBHistCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {listRow partRows sumRow weakRows boundaryRow routeLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory listRow ->
      UnaryHistory partRows ->
        UnaryHistory weakRows ->
          UnaryHistory routeLedger ->
            UnaryHistory provenance ->
              Cont listRow partRows sumRow ->
                Cont sumRow weakRows boundaryRow ->
                  Cont boundaryRow routeLedger endpoint ->
                    PkgSig bundle endpoint pkg ->
                      UnaryHistory sumRow ∧ UnaryHistory boundaryRow ∧
                        UnaryHistory endpoint ∧ hsame sumRow (append listRow partRows) ∧
                          hsame boundaryRow (append sumRow weakRows) ∧
                            hsame endpoint (append boundaryRow routeLedger) ∧
                              PkgSig bundle endpoint pkg := by
  intro listUnary partUnary weakUnary routeUnary _provenanceUnary listPartRow weakBoundaryRow
    routeEndpointRow pkgSig
  have sumUnary : UnaryHistory sumRow :=
    unary_cont_closed listUnary partUnary listPartRow
  have boundaryUnary : UnaryHistory boundaryRow :=
    unary_cont_closed sumUnary weakUnary weakBoundaryRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed boundaryUnary routeUnary routeEndpointRow
  exact
    And.intro sumUnary
      (And.intro boundaryUnary
        (And.intro endpointUnary
          (And.intro listPartRow
            (And.intro weakBoundaryRow
              (And.intro routeEndpointRow pkgSig)))))

theorem PartitionBHistCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              row bundle pkg)
        (fun row : BHist =>
          exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              row bundle pkg)
        (fun row : BHist =>
          exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              row bundle pkg)
        (fun h k : BHist =>
          (exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              h bundle pkg) ∧
            (exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
              PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
                k bundle pkg) ∧
              hsame h k) := by
  intro carrier
  let SourceSpec : BHist -> Prop := fun row =>
    exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
      PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance row
        bundle pkg
  have endpointSource : SourceSpec endpoint := by
    exact
      ⟨listRow, partRows, sumRow, decreaseRows, boundary, route, provenance, carrier⟩
  constructor
  · constructor
    · exact ⟨endpoint, endpointSource⟩
    · intro h source
      exact ⟨source, source, hsame_refl h⟩
    · intro h k classified
      exact ⟨classified.right.left, classified.left, hsame_symm classified.right.right⟩
    · intro h k r classifiedHK classifiedKR
      exact
        ⟨classifiedHK.left, classifiedKR.right.left,
          hsame_trans classifiedHK.right.right classifiedKR.right.right⟩
    · intro h k classified _source
      exact classified.right.left
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.PartitionUp
