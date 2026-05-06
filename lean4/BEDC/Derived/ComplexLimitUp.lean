import BEDC.FKernel.Unary
import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexDistance (z w d : BHist) : Prop :=
  UnaryHistory z ∧ UnaryHistory w ∧ UnaryHistory d ∧ (Cont z w d ∨ Cont w z d)

def ComplexDistanceTriangleBound (d12 d23 : BHist) : BHist :=
  append d12 d23

theorem ComplexDistanceTriangleBound_unary_of_distances {z w u d12 d23 : BHist} :
    ComplexDistance z w d12 -> ComplexDistance w u d23 ->
      UnaryHistory (ComplexDistanceTriangleBound d12 d23) ∧ UnaryHistory z ∧ UnaryHistory u := by
  intro leftDistance rightDistance
  have boundUnary : UnaryHistory (ComplexDistanceTriangleBound d12 d23) :=
    unary_append_closed leftDistance.right.right.left rightDistance.right.right.left
  exact And.intro boundUnary (And.intro leftDistance.left rightDistance.right.left)

theorem ComplexDistanceTriangleBound_empty_endpoints {z w u d12 d23 : BHist} :
    ComplexDistance z w d12 -> ComplexDistance w u d23 ->
      hsame (ComplexDistanceTriangleBound d12 d23) BHist.Empty ->
        hsame z BHist.Empty ∧ hsame w BHist.Empty ∧ hsame u BHist.Empty := by
  intro leftDistance rightDistance boundEmpty
  have distanceEmpty := append_eq_empty_iff.mp boundEmpty
  cases distanceEmpty.left
  cases distanceEmpty.right
  have leftEndpoints : hsame z BHist.Empty ∧ hsame w BHist.Empty := by
    cases leftDistance with
    | intro _zCarrier rest =>
        cases rest with
        | intro _wCarrier rest =>
            cases rest with
            | intro _dCarrier rel =>
                cases rel with
                | inl zw =>
                    exact cont_empty_result_inversion zw
                | inr wz =>
                    have endpoints := cont_empty_result_inversion wz
                    exact And.intro endpoints.right endpoints.left
  have rightEndpoints : hsame w BHist.Empty ∧ hsame u BHist.Empty := by
    cases rightDistance with
    | intro _wCarrier rest =>
        cases rest with
        | intro _uCarrier rest =>
            cases rest with
            | intro _dCarrier rel =>
                cases rel with
                | inl wu =>
                    exact cont_empty_result_inversion wu
                | inr uw =>
                    have endpoints := cont_empty_result_inversion uw
                    exact And.intro endpoints.right endpoints.left
  exact And.intro leftEndpoints.left (And.intro leftEndpoints.right rightEndpoints.right)
theorem ComplexDistance_triangle_explicit_bound {z w u d12 d23 : BHist} : ComplexDistance z w d12 ->
    ComplexDistance w u d23 -> exists d13 : BHist, ComplexDistance z u d13 ∧
      Cont d12 d23 (ComplexDistanceTriangleBound d12 d23) ∧
        UnaryHistory (ComplexDistanceTriangleBound d12 d23) := by
  intro leftDistance rightDistance
  exact Exists.intro (append z u)
    (And.intro (And.intro leftDistance.left (And.intro rightDistance.right.left (And.intro
        (unary_append_closed leftDistance.left rightDistance.right.left) (Or.inl (cont_intro rfl)))))
      (And.intro (cont_intro rfl)
        (unary_append_closed leftDistance.right.right.left rightDistance.right.right.left)))
theorem ComplexDistance_append_constant_closed {z w d q : BHist} :
    UnaryHistory q -> ComplexDistance z w d ->
      ComplexDistance (append z q) (append w q) (append (append z q) (append w q)) := by
  intro unaryQ distance
  have leftUnary : UnaryHistory (append z q) := unary_append_closed distance.left unaryQ
  have rightUnary : UnaryHistory (append w q) := unary_append_closed distance.right.left unaryQ
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro (unary_append_closed leftUnary rightUnary) (Or.inl (cont_intro rfl))))

theorem ComplexDistance_prepend_constant_closed {z w d q : BHist} :
    UnaryHistory q -> ComplexDistance z w d ->
      ComplexDistance (append q z) (append q w) (append (append q z) (append q w)) := by
  intro unaryQ distance
  have leftUnary : UnaryHistory (append q z) := unary_append_closed unaryQ distance.left
  have rightUnary : UnaryHistory (append q w) := unary_append_closed unaryQ distance.right.left
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro (unary_append_closed leftUnary rightUnary) (Or.inl (cont_intro rfl))))

theorem ComplexDistance_append_constant_result_deterministic {z w d q d' : BHist} :
    UnaryHistory q -> ComplexDistance z w d -> ComplexDistance (append z q) (append w q) d' ->
      hsame d' (append (append z q) (append w q)) := by
  intro _unaryQ _distance shiftedDistance
  cases shiftedDistance.right.right.right with
  | inl forward =>
      exact cont_deterministic forward (cont_intro rfl)
  | inr reverse =>
      have sameReverse : hsame d' (append (append w q) (append z q)) :=
        cont_deterministic reverse (cont_intro rfl)
      have sameCanonical :
          hsame (append (append w q) (append z q)) (append (append z q) (append w q)) :=
        unary_append_comm_hsame shiftedDistance.right.left shiftedDistance.left
      exact hsame_trans sameReverse sameCanonical

theorem ComplexDistance_prepend_constant_result_deterministic {z w d q d' : BHist} :
    UnaryHistory q -> ComplexDistance z w d -> ComplexDistance (append q z) (append q w) d' ->
      hsame d' (append (append q z) (append q w)) := by
  intro _unaryQ _distance shiftedDistance
  cases shiftedDistance.right.right.right with
  | inl forward =>
      exact cont_deterministic forward (cont_intro rfl)
  | inr reverse =>
      have sameReverse : hsame d' (append (append q w) (append q z)) :=
        cont_deterministic reverse (cont_intro rfl)
      have sameCanonical :
          hsame (append (append q w) (append q z)) (append (append q z) (append q w)) :=
        unary_append_comm_hsame shiftedDistance.right.left shiftedDistance.left
      exact hsame_trans sameReverse sameCanonical

theorem ComplexDistance_symm_iff {z w d : BHist} :
    (ComplexDistance z w d ↔ ComplexDistance w z d) ∧
      (ComplexDistance z w d -> UnaryHistory z ∧ UnaryHistory w ∧ UnaryHistory d) := by
  constructor
  · constructor
    · intro distance
      cases distance with
      | intro zCarrier rest =>
          cases rest with
          | intro wCarrier rest =>
              cases rest with
              | intro dCarrier rel =>
                  exact
                    And.intro wCarrier
                      (And.intro zCarrier
                        (And.intro dCarrier
                          (Or.elim rel
                            (fun zw => Or.inr zw)
                            (fun wz => Or.inl wz))))
    · intro distance
      cases distance with
      | intro wCarrier rest =>
          cases rest with
          | intro zCarrier rest =>
              cases rest with
              | intro dCarrier rel =>
                  exact
                    And.intro zCarrier
                      (And.intro wCarrier
                        (And.intro dCarrier
                          (Or.elim rel
                            (fun wz => Or.inr wz)
                            (fun zw => Or.inl zw))))
  · intro distance
    exact And.intro distance.left (And.intro distance.right.left distance.right.right.left)

theorem ComplexDistance_empty_left_iff {w d : BHist} :
    ComplexDistance BHist.Empty w d <-> UnaryHistory w ∧ hsame d w := by
  constructor
  · intro distance
    have same : hsame d w :=
      Or.elim distance.right.right.right
        (fun left => cont_left_unit_result left)
        (fun right => Iff.mp cont_right_unit_iff right)
    exact And.intro distance.right.left same
  · intro data
    have dUnary : UnaryHistory d :=
      unary_transport data.left (hsame_symm data.right)
    have leftContinuation : Cont BHist.Empty w d :=
      Iff.mpr cont_left_unit_iff data.right
    exact And.intro unary_empty
      (And.intro data.left (And.intro dUnary (Or.inl leftContinuation)))

theorem ComplexDistance_hsame_transport_with_relation {z z' w w' d d' : BHist} :
    hsame z z' -> hsame w w' -> hsame d d' -> ComplexDistance z w d ->
      ComplexDistance z' w' d' ∧ (Cont z' w' d' ∨ Cont w' z' d') := by
  intro sameZ sameW sameD distance
  have zUnary : UnaryHistory z' := unary_transport distance.left sameZ
  have wUnary : UnaryHistory w' := unary_transport distance.right.left sameW
  have dUnary : UnaryHistory d' := unary_transport distance.right.right.left sameD
  have relation : Cont z' w' d' ∨ Cont w' z' d' :=
    Or.elim distance.right.right.right
      (fun left => by
        cases sameZ
        cases sameW
        exact Or.inl (cont_result_hsame_transport left sameD))
      (fun right => by
        cases sameZ
        cases sameW
        exact Or.inr (cont_result_hsame_transport right sameD))
  exact And.intro (And.intro zUnary (And.intro wUnary (And.intro dUnary relation))) relation

theorem ComplexDistance_empty_iff {z w : BHist} :
    ComplexDistance z w BHist.Empty ↔
      UnaryHistory z ∧ UnaryHistory w ∧ hsame z BHist.Empty ∧ hsame w BHist.Empty := by
  constructor
  · intro distance
    cases distance.right.right.right with
    | inl zw =>
        have endpoints := cont_empty_result_inversion zw
        exact And.intro distance.left
          (And.intro distance.right.left (And.intro endpoints.left endpoints.right))
    | inr wz =>
        have endpoints := cont_empty_result_inversion wz
        exact And.intro distance.left
          (And.intro distance.right.left (And.intro endpoints.right endpoints.left))
  · intro endpoints
    cases endpoints.right.right.left
    cases endpoints.right.right.right
    exact And.intro endpoints.left
      (And.intro endpoints.right.left
        (And.intro unary_empty (Or.inl (cont_left_unit BHist.Empty))))

theorem ComplexDistance_empty_left_endpoint_iff {w d : BHist} :
    ComplexDistance BHist.Empty w d ↔ UnaryHistory w ∧ hsame d w := by
  constructor
  · intro distance
    cases distance.right.right.right with
    | inl ew =>
        exact And.intro distance.right.left (cont_left_unit_result ew)
    | inr we =>
        exact And.intro distance.right.left (cont_right_unit_iff.mp we)
  · intro data
    cases data.right
    exact And.intro unary_empty
      (And.intro data.left
        (And.intro data.left (Or.inl (cont_left_unit w))))

theorem ComplexDistance_empty_endpoint_iff {z w : BHist} :
    ComplexDistance z w BHist.Empty ↔
      UnaryHistory z ∧ UnaryHistory w ∧ hsame z BHist.Empty ∧ hsame w BHist.Empty :=
  ComplexDistance_empty_iff

def ComplexRegularSequence (s N : BHist -> BHist) : Prop :=
  forall k n m : BHist, UnaryHistory k -> UnaryHistory n -> UnaryHistory m ->
    Cont (N k) n n -> Cont (N k) m m ->
      exists d : BHist, ComplexDistance (s n) (s m) d

def ComplexPointwiseSum (s t : BHist -> BHist) (n : BHist) : BHist :=
  append (s n) (t n)

def ComplexLimit (s N : BHist -> BHist) (z : BHist) (M : BHist -> BHist) : Prop :=
  ComplexRegularSequence s N ∧ ComplexHistoryCarrier z ∧
    forall k n : BHist, UnaryHistory k -> UnaryHistory n -> Cont (M k) n n ->
      exists d : BHist, ComplexDistance (s n) z d

def ComplexLimitPatternSpec (s M : BHist -> BHist) (z k n d : BHist) : Prop :=
  UnaryHistory k ∧ UnaryHistory n ∧ Cont (M k) n n ∧ ComplexDistance (s n) z d

theorem ComplexLimitPatternSpec_of_limit {s N M : BHist -> BHist} {z k n : BHist} :
    ComplexLimit s N z M -> UnaryHistory k -> UnaryHistory n -> Cont (M k) n n ->
      exists d : BHist, ComplexLimitPatternSpec s M z k n d := by
  intro limit unaryK unaryN controlled
  cases limit with
  | intro _regular rest =>
      cases rest with
      | intro _carrierZ modulus =>
          cases modulus k n unaryK unaryN controlled with
          | intro d distance =>
              exact Exists.intro d
                (And.intro unaryK (And.intro unaryN (And.intro controlled distance)))

theorem ComplexLimit_hsame_transport {s N M : BHist -> BHist} {z z' : BHist} :
    hsame z z' -> ComplexLimit s N z M -> ComplexLimit s N z' M := by
  intro sameZ limit
  cases limit with
  | intro regular limitRest =>
      cases limitRest with
      | intro carrierZ modulus =>
          have carrierZ' : ComplexHistoryCarrier z' :=
            ComplexHistoryLedgerPolicy_visible_carrier (And.intro carrierZ sameZ)
          exact And.intro regular
            (And.intro carrierZ'
              (fun k n unaryK unaryN controlled =>
                match modulus k n unaryK unaryN controlled with
                | Exists.intro d distance =>
                    Exists.intro d
                      (ComplexDistance_hsame_transport_with_relation
                        (hsame_refl (s n)) sameZ (hsame_refl d) distance).left))

theorem ComplexLimit_semanticNameCert {s N M : BHist -> BHist} {z : BHist}
    (limit : ComplexLimit s N z M) :
    SemanticNameCert (fun h : BHist => ComplexLimit s N h M)
      (fun h : BHist => ComplexLimit s N h M) (fun h : BHist => ComplexLimit s N h M)
      hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro z limit
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        exact ComplexLimit_hsame_transport sameHK sourceH
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem ComplexRegularSequence_constant {z : BHist} :
    UnaryHistory z -> ComplexRegularSequence (fun _ : BHist => z)
      (fun _ : BHist => BHist.Empty) := by
  intro zUnary
  intro k n m unaryK unaryN unaryM contN contM
  exact Exists.intro (append z z)
    (And.intro zUnary
      (And.intro zUnary
        (And.intro (unary_append_closed zUnary zUnary) (Or.inl (cont_intro rfl)))))

theorem ComplexLimit_constant {z : BHist} :
    ComplexHistoryCarrier z ->
      ComplexLimit (fun _ : BHist => z) (fun _ : BHist => BHist.Empty) z
        (fun _ : BHist => BHist.Empty) := by
  intro carrierZ
  have zUnary : UnaryHistory z := ComplexHistoryCarrier_unary carrierZ
  exact And.intro (ComplexRegularSequence_constant zUnary)
    (And.intro carrierZ
      (fun k n unaryK unaryN controlled =>
        Exists.intro (append z z)
          (And.intro zUnary
            (And.intro zUnary
              (And.intro (unary_append_closed zUnary zUnary) (Or.inl (cont_intro rfl)))))))

theorem ComplexLimit_eventually_constant_closed {s N M : BHist -> BHist} {z : BHist} :
    ComplexRegularSequence s N -> ComplexHistoryCarrier z ->
      (forall {k n : BHist}, UnaryHistory k -> UnaryHistory n -> Cont (M k) n n ->
        hsame (s n) z) ->
        ComplexLimit s N z M := by
  intro regular carrierZ eventuallyConstant
  have zUnary : UnaryHistory z := ComplexHistoryCarrier_unary carrierZ
  exact And.intro regular
    (And.intro carrierZ
      (fun k n unaryK unaryN controlled =>
        let constantDistance : ComplexDistance z z (append z z) :=
          And.intro zUnary
            (And.intro zUnary
              (And.intro (unary_append_closed zUnary zUnary) (Or.inl (cont_intro rfl))))
        Exists.intro (append z z)
          (ComplexDistance_hsame_transport_with_relation
            (hsame_symm (eventuallyConstant unaryK unaryN controlled))
            (hsame_refl z) (hsame_refl (append z z)) constantDistance).left))

theorem ComplexRegularSequence_hsame_transport {s t N : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) (t n)) ->
      ComplexRegularSequence s N -> ComplexRegularSequence t N := by
  intro pointwise regular
  intro k n m unaryK unaryN unaryM contN contM
  cases regular k n m unaryK unaryN unaryM contN contM with
  | intro d distance =>
      exact Exists.intro d
        (ComplexDistance_hsame_transport_with_relation
          (pointwise unaryN) (pointwise unaryM) (hsame_refl d) distance).left

theorem ComplexRegularSequence_pointwise_sum_closed {s t N : BHist -> BHist} :
    ComplexRegularSequence s N -> ComplexRegularSequence t N ->
      ComplexRegularSequence (ComplexPointwiseSum s t) N := by
  intro regularS regularT
  intro k n m unaryK unaryN unaryM contN contM
  cases regularS k n m unaryK unaryN unaryM contN contM with
  | intro _ds distanceS =>
      cases regularT k n m unaryK unaryN unaryM contN contM with
      | intro _dt distanceT =>
          have leftUnary : UnaryHistory (ComplexPointwiseSum s t n) :=
            unary_append_closed distanceS.left distanceT.left
          have rightUnary : UnaryHistory (ComplexPointwiseSum s t m) :=
            unary_append_closed distanceS.right.left distanceT.right.left
          exact Exists.intro
            (append (ComplexPointwiseSum s t n) (ComplexPointwiseSum s t m))
            (And.intro leftUnary
              (And.intro rightUnary
                (And.intro (unary_append_closed leftUnary rightUnary)
                  (Or.inl (cont_intro rfl)))))

theorem ComplexLimit_sequence_hsame_transport {s t N M : BHist -> BHist} {z : BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (s n) (t n)) ->
      ComplexLimit s N z M -> ComplexLimit t N z M := by
  intro pointwise limit
  cases limit with
  | intro regular rest =>
      cases rest with
      | intro carrierZ modulus =>
          exact And.intro (ComplexRegularSequence_hsame_transport pointwise regular)
            (And.intro carrierZ
              (fun k n unaryK unaryN controlled =>
                match modulus k n unaryK unaryN controlled with
                | Exists.intro d distance =>
                    Exists.intro d
                      (ComplexDistance_hsame_transport_with_relation
                        (pointwise unaryN) (hsame_refl z) (hsame_refl d) distance).left))

theorem ComplexRegularSequence_append_constant_closed {s N : BHist -> BHist} {q : BHist} :
    UnaryHistory q -> ComplexRegularSequence s N ->
      ComplexRegularSequence (fun n : BHist => append (s n) q) N := by
  intro unaryQ regular
  intro k n m unaryK unaryN unaryM contN contM
  cases regular k n m unaryK unaryN unaryM contN contM with
  | intro d distance =>
      have leftUnary : UnaryHistory (append (s n) q) := unary_append_closed distance.left unaryQ
      have rightUnary : UnaryHistory (append (s m) q) :=
        unary_append_closed distance.right.left unaryQ
      exact Exists.intro (append (append (s n) q) (append (s m) q))
        (And.intro leftUnary
          (And.intro rightUnary
            (And.intro (unary_append_closed leftUnary rightUnary) (Or.inl (cont_intro rfl)))))

theorem ComplexLimit_append_constant_closed {s N M : BHist -> BHist} {z q : BHist} :
    UnaryHistory q -> ComplexLimit s N z M ->
      ComplexLimit (fun n : BHist => append (s n) q) N (append z q) M := by
  intro unaryQ limit
  cases limit with
  | intro regular rest =>
      cases rest with
      | intro carrierZ modulus =>
          exact And.intro (ComplexRegularSequence_append_constant_closed unaryQ regular)
            (And.intro (ComplexHistoryCarrier_append_unary_closed carrierZ unaryQ)
              (fun k n unaryK unaryN controlled =>
                match modulus k n unaryK unaryN controlled with
                | Exists.intro d distance =>
                    Exists.intro (append (append (s n) q) (append z q))
                      (ComplexDistance_append_constant_closed unaryQ distance)))

theorem ComplexRegularSequence_pointwise_append_same_modulus_closed {s t N : BHist -> BHist} :
    ComplexRegularSequence s N -> ComplexRegularSequence t N ->
      ComplexRegularSequence (fun n : BHist => append (s n) (t n)) N := by
  intro regularS regularT
  intro k n m unaryK unaryN unaryM contN contM
  cases regularS k n m unaryK unaryN unaryM contN contM with
  | intro dS distanceS =>
      cases regularT k n m unaryK unaryN unaryM contN contM with
      | intro dT distanceT =>
          have leftUnary : UnaryHistory (append (s n) (t n)) :=
            unary_append_closed distanceS.left distanceT.left
          have rightUnary : UnaryHistory (append (s m) (t m)) :=
            unary_append_closed distanceS.right.left distanceT.right.left
          exact Exists.intro (append (append (s n) (t n)) (append (s m) (t m)))
            (And.intro leftUnary
              (And.intro rightUnary
                (And.intro (unary_append_closed leftUnary rightUnary)
                  (Or.inl (cont_intro rfl)))))

theorem ComplexLimit_pointwise_append_same_modulus_closed {s t N M : BHist -> BHist}
    {z w : BHist} :
    ComplexLimit s N z M -> ComplexLimit t N w M ->
      ComplexLimit (fun n : BHist => append (s n) (t n)) N (append z w) M := by
  intro limitS limitT
  cases limitS with
  | intro regularS restS =>
      cases restS with
      | intro carrierZ modulusS =>
          cases limitT with
          | intro regularT restT =>
              cases restT with
              | intro carrierW modulusT =>
                  have zUnary : UnaryHistory z := ComplexHistoryCarrier_unary carrierZ
                  have carrierZW : ComplexHistoryCarrier (append z w) :=
                    ComplexHistoryCarrier_append_unary_closed carrierZ
                      (ComplexHistoryCarrier_unary carrierW)
                  exact And.intro
                    (ComplexRegularSequence_pointwise_append_same_modulus_closed
                      regularS regularT)
                    (And.intro carrierZW
                      (fun k n unaryK unaryN controlled =>
                        match modulusS k n unaryK unaryN controlled with
                        | Exists.intro dS distanceS =>
                            match modulusT k n unaryK unaryN controlled with
                            | Exists.intro dT distanceT =>
                                have leftUnary : UnaryHistory (append (s n) (t n)) :=
                                  unary_append_closed distanceS.left distanceT.left
                                have rightUnary : UnaryHistory (append z w) :=
                                  unary_append_closed zUnary distanceT.right.left
                                Exists.intro (append (append (s n) (t n)) (append z w))
                                  (And.intro leftUnary
                                    (And.intro rightUnary
                                      (And.intro (unary_append_closed leftUnary rightUnary)
                                        (Or.inl (cont_intro rfl)))))))

theorem ComplexRegularSequence_append_constant_result_deterministic {s N : BHist -> BHist}
    {q k n m d' : BHist} :
    UnaryHistory q -> ComplexRegularSequence s N -> UnaryHistory k -> UnaryHistory n ->
      UnaryHistory m -> Cont (N k) n n -> Cont (N k) m m ->
        ComplexDistance (append (s n) q) (append (s m) q) d' ->
          hsame d' (append (append (s n) q) (append (s m) q)) := by
  intro unaryQ regular unaryK unaryN unaryM contN contM shiftedDistance
  cases regular k n m unaryK unaryN unaryM contN contM with
  | intro d distance =>
      exact ComplexDistance_append_constant_result_deterministic unaryQ distance shiftedDistance

theorem ComplexRegularSequence_prepend_constant_closed {s N : BHist -> BHist} {q : BHist} :
    UnaryHistory q -> ComplexRegularSequence s N ->
      ComplexRegularSequence (fun n : BHist => append q (s n)) N := by
  intro unaryQ regular
  intro k n m unaryK unaryN unaryM contN contM
  cases regular k n m unaryK unaryN unaryM contN contM with
  | intro d distance =>
      have leftUnary : UnaryHistory (append q (s n)) := unary_append_closed unaryQ distance.left
      have rightUnary : UnaryHistory (append q (s m)) :=
        unary_append_closed unaryQ distance.right.left
      exact Exists.intro (append (append q (s n)) (append q (s m)))
        (And.intro leftUnary
          (And.intro rightUnary
            (And.intro (unary_append_closed leftUnary rightUnary) (Or.inl (cont_intro rfl)))))

theorem ComplexDistance_empty_source_iff {w d : BHist} :
    ComplexDistance BHist.Empty w d ↔ UnaryHistory w ∧ hsame d w := by
  constructor
  · intro distance
    cases distance with
    | intro _emptyCarrier rest =>
        cases rest with
        | intro wCarrier rest =>
            cases rest with
            | intro _dCarrier rel =>
                constructor
                · exact wCarrier
                · cases rel with
                  | inl leftRel =>
                      exact cont_left_unit_result leftRel
                  | inr rightRel =>
                      exact Iff.mp cont_right_unit_iff rightRel
  · intro data
    have dCarrier : UnaryHistory d := unary_transport data.left (hsame_symm data.right)
    exact And.intro unary_empty
      (And.intro data.left
        (And.intro dCarrier (Or.inl (Iff.mpr cont_left_unit_iff data.right))))
theorem ComplexDistance_nonempty_distance_endpoint_cases {z w d : BHist} :
    ComplexDistance z w d -> (hsame d BHist.Empty -> False) ->
      (hsame z BHist.Empty -> False) \/ (hsame w BHist.Empty -> False) := by
  intro distance distanceNonempty
  cases distance.right.right.right with
  | inl zw =>
      exact Iff.mp append_nonempty_iff (fun appendEmpty => distanceNonempty (zw.trans appendEmpty))
  | inr wz =>
      have endpointCases :
          (hsame w BHist.Empty -> False) \/ (hsame z BHist.Empty -> False) :=
        Iff.mp append_nonempty_iff (fun appendEmpty => distanceNonempty (wz.trans appendEmpty))
      cases endpointCases with
      | inl wNonempty =>
          exact Or.inr wNonempty
      | inr zNonempty =>
          exact Or.inl zNonempty

theorem ComplexDistance_endpoint_nonempty_distance_nonempty {z w d : BHist} :
    ComplexDistance z w d ->
      ((hsame z BHist.Empty -> False) ∨ (hsame w BHist.Empty -> False)) ->
        hsame d BHist.Empty -> False := by
  intro distance endpointNonempty dEmpty
  cases distance.right.right.right with
  | inl zw =>
      have emptyParts := cont_empty_result_inversion (cont_result_hsame_transport zw dEmpty)
      cases endpointNonempty with
      | inl zNonempty =>
          exact zNonempty emptyParts.left
      | inr wNonempty =>
          exact wNonempty emptyParts.right
  | inr wz =>
      have emptyParts := cont_empty_result_inversion (cont_result_hsame_transport wz dEmpty)
      cases endpointNonempty with
      | inl zNonempty =>
          exact zNonempty emptyParts.right
      | inr wNonempty =>
          exact wNonempty emptyParts.left

theorem ComplexDistanceTriangleBound_unary {z w u d12 d23 : BHist} :
    ComplexDistance z w d12 -> ComplexDistance w u d23 ->
      UnaryHistory (ComplexDistanceTriangleBound d12 d23) := by
  intro leftDistance rightDistance
  exact unary_append_closed leftDistance.right.right.left rightDistance.right.right.left

theorem ComplexDistance_unary_append_comm_package {z q : BHist} :
    UnaryHistory z -> UnaryHistory q ->
      ComplexDistance (append q z) (append z q) (append (append q z) (append z q)) ∧
        hsame (append q z) (append z q) := by
  intro zCarrier qCarrier
  have leftCarrier : UnaryHistory (append q z) := unary_append_closed qCarrier zCarrier
  have rightCarrier : UnaryHistory (append z q) := unary_append_closed zCarrier qCarrier
  exact And.intro
    (And.intro leftCarrier
      (And.intro rightCarrier
        (And.intro (unary_append_closed leftCarrier rightCarrier) (Or.inl (cont_intro rfl)))))
    (unary_append_comm_hsame qCarrier zCarrier)

end BEDC.Derived.ComplexLimitUp
