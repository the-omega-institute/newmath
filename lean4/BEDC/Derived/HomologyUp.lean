import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont

namespace BEDC.Derived.HomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont

def HomologySingletonCycleCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def HomologySingletonCycleClassifier (h k : BHist) : Prop :=
  HomologySingletonCycleCarrier h ∧ HomologySingletonCycleCarrier k ∧ hsame h k

theorem HomologySingletonCycle_semanticNameCert :
    SemanticNameCert HomologySingletonCycleCarrier HomologySingletonCycleCarrier
      HomologySingletonCycleCarrier HomologySingletonCycleClassifier := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _carrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

def HomologyCycleCarrier (d : BHist -> BHist) (h : BHist) : Prop :=
  hsame (d h) BHist.Empty

def HomologyBoundaryCarrier (d : BHist -> BHist) (h : BHist) : Prop :=
  Exists (fun u : BHist => hsame h (d u))

theorem HomologyBoundaryCarrier_nonempty_preimage {d : BHist -> BHist} {h : BHist} :
    HomologyBoundaryCarrier d h -> (hsame h BHist.Empty -> False) ->
      Exists (fun u : BHist => hsame h (d u) ∧ (hsame (d u) BHist.Empty -> False)) := by
  intro boundary hNonempty
  cases boundary with
  | intro u witness =>
      exact Exists.intro u
        (And.intro witness (fun duEmpty => hNonempty (hsame_trans witness duEmpty)))

theorem HomologyBoundaryCarrier_empty_preimage {d : BHist -> BHist} {h : BHist} :
    HomologyBoundaryCarrier d h -> hsame h BHist.Empty ->
      Exists (fun u : BHist => hsame h (d u) ∧ hsame (d u) BHist.Empty) := by
  intro boundary hEmpty
  cases boundary with
  | intro u witness =>
      exact Exists.intro u (And.intro witness (hsame_trans (hsame_symm witness) hEmpty))

theorem HomologyBoundaryCarrier_cycle_closed {d : BHist -> BHist}
    (d_squared_zero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    {h : BHist} :
    HomologyBoundaryCarrier d h -> HomologyCycleCarrier d h := by
  intro boundary
  cases boundary with
  | intro u witness =>
      cases witness
      exact d_squared_zero u

theorem HomologyCycleCarrier_append_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyCycleCarrier d h -> HomologyCycleCarrier d k ->
      HomologyCycleCarrier d (append h k) := by
  intro cycleH cycleK
  exact hsame_trans (dAppend h k) (by
    have dhEmpty : d h = BHist.Empty := hsame_empty_iff.mp cycleH
    have dkEmpty : d k = BHist.Empty := hsame_empty_iff.mp cycleK
    exact append_eq_empty_iff.mpr (And.intro dhEmpty dkEmpty))

theorem HomologyBoundaryCarrier_append_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k ->
      HomologyBoundaryCarrier d (append h k) := by
  intro boundaryH boundaryK
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          exact Exists.intro (append u v)
            (hsame_trans appendWitness (hsame_symm (dAppend u v)))

theorem HomologyBoundaryCarrier_append_hsame_transport {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k r : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k -> hsame (append h k) r ->
      HomologyBoundaryCarrier d r := by
  intro boundaryH boundaryK sameResult
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          exact Exists.intro (append u v)
            (hsame_trans (hsame_symm sameResult)
              (hsame_trans appendWitness (hsame_symm (dAppend u v))))

theorem HomologyBoundaryCarrier_cont_preimage {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k r : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k -> Cont h k r ->
      Exists (fun u : BHist => Exists (fun v : BHist => Exists (fun uv : BHist =>
        Cont u v uv ∧ hsame r (d uv) ∧ hsame h (d u) ∧ hsame k (d v)))) := by
  intro boundaryH boundaryK continuation
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          exact Exists.intro u
            (Exists.intro v
              (Exists.intro (append u v)
                (And.intro (cont_intro rfl)
                  (And.intro
                    (hsame_trans continuation
                      (hsame_trans appendWitness (hsame_symm (dAppend u v))))
                    (And.intro witnessH witnessK)))))

theorem HomologyBoundaryCarrier_cont_preimage_append {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k r : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k -> Cont h k r ->
      Exists (fun u : BHist => Exists (fun v : BHist =>
        hsame h (d u) ∧ hsame k (d v) ∧ hsame r (d (append u v)))) := by
  intro boundaryH boundaryK resultRel
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          exact Exists.intro u
            (Exists.intro v
              (And.intro witnessH
                (And.intro witnessK
                  (hsame_trans resultRel
                    (hsame_trans appendWitness (hsame_symm (dAppend u v)))))))

theorem HomologyBoundaryCarrier_cont_nonempty_preimage_append {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k r : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k -> Cont h k r ->
      (hsame r BHist.Empty -> False) ->
        Exists (fun u : BHist => Exists (fun v : BHist =>
          hsame h (d u) ∧ hsame k (d v) ∧
            (hsame (d (append u v)) BHist.Empty -> False))) := by
  intro boundaryH boundaryK resultRel resultNonempty
  cases boundaryH with
  | intro u witnessH =>
      cases boundaryK with
      | intro v witnessK =>
          have appendWitness : hsame (append h k) (append (d u) (d v)) := by
            cases witnessH
            cases witnessK
            exact hsame_refl (append (d u) (d v))
          have resultWitness : hsame r (d (append u v)) :=
            hsame_trans resultRel
              (hsame_trans appendWitness (hsame_symm (dAppend u v)))
          exact Exists.intro u
            (Exists.intro v
              (And.intro witnessH
                (And.intro witnessK
                  (fun dAppendEmpty => resultNonempty
                    (hsame_trans resultWitness dAppendEmpty)))))

theorem HomologyBoundaryCarrier_append_empty_preimages {d : BHist -> BHist} {h k : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k ->
      hsame (append h k) BHist.Empty ->
        Exists (fun u : BHist =>
          Exists (fun v : BHist =>
            hsame h (d u) ∧ hsame k (d v) ∧
              hsame (d u) BHist.Empty ∧ hsame (d v) BHist.Empty)) := by
  intro boundaryH boundaryK appendEmpty
  have emptyParts : h = BHist.Empty ∧ k = BHist.Empty :=
    append_eq_empty_iff.mp (hsame_empty_iff.mp appendEmpty)
  have hEmpty : hsame h BHist.Empty := emptyParts.left
  have kEmpty : hsame k BHist.Empty := emptyParts.right
  have hPreimage := HomologyBoundaryCarrier_empty_preimage boundaryH hEmpty
  have kPreimage := HomologyBoundaryCarrier_empty_preimage boundaryK kEmpty
  cases hPreimage with
  | intro u hData =>
      cases kPreimage with
      | intro v kData =>
          exact Exists.intro u
            (Exists.intro v
              (And.intro hData.left
                (And.intro kData.left (And.intro hData.right kData.right))))

theorem HomologyBoundaryCarrier_append_nonempty_preimage {d : BHist -> BHist} {h k : BHist} :
    HomologyBoundaryCarrier d h -> HomologyBoundaryCarrier d k ->
      (hsame (append h k) BHist.Empty -> False) ->
        (Exists (fun u : BHist =>
          hsame h (d u) ∧ (hsame (d u) BHist.Empty -> False))) ∨
          (Exists (fun v : BHist =>
            hsame k (d v) ∧ (hsame (d v) BHist.Empty -> False))) := by
  intro boundaryH boundaryK appendNonempty
  have nonemptyParts := append_nonempty_iff.mp appendNonempty
  cases nonemptyParts with
  | inl hNonempty =>
      exact Or.inl (HomologyBoundaryCarrier_nonempty_preimage boundaryH hNonempty)
  | inr kNonempty =>
      exact Or.inr (HomologyBoundaryCarrier_nonempty_preimage boundaryK kNonempty)

theorem HomologyBoundaryCarrier_cycle_of_d_squared_zero {d : BHist -> BHist}
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    (dSquaredZero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    {h : BHist} :
    HomologyBoundaryCarrier d h -> HomologyCycleCarrier d h := by
  intro boundaryH
  cases boundaryH with
  | intro u witness =>
      exact hsame_trans (dCongr witness) (dSquaredZero u)

theorem HomologyCycleCarrier_append_hsame_transport {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    {h k r : BHist} :
    HomologyCycleCarrier d h -> HomologyCycleCarrier d k -> hsame (append h k) r ->
      HomologyCycleCarrier d r := by
  intro cycleH cycleK sameResult
  exact hsame_trans (hsame_symm (dCongr sameResult))
    (HomologyCycleCarrier_append_closed dAppend cycleH cycleK)

theorem HomologyCycleCarrier_append_components_iff {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    {h k : BHist} :
    HomologyCycleCarrier d (append h k) ↔
      HomologyCycleCarrier d h ∧ HomologyCycleCarrier d k := by
  constructor
  · intro cycleAppend
    have componentEmpty : hsame (append (d h) (d k)) BHist.Empty :=
      hsame_trans (hsame_symm (dAppend h k)) cycleAppend
    have endpoints := append_eq_empty_iff.mp componentEmpty
    exact And.intro endpoints.left endpoints.right
  · intro cycles
    exact HomologyCycleCarrier_append_closed dAppend cycles.left cycles.right

theorem HomologyCycleBoundary_append_cycle_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (d_squared_zero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    {h k : BHist} :
    HomologyCycleCarrier d h -> HomologyBoundaryCarrier d k ->
      HomologyCycleCarrier d (append h k) := by
  intro cycleH boundaryK
  exact HomologyCycleCarrier_append_closed dAppend cycleH
    (HomologyBoundaryCarrier_cycle_closed d_squared_zero boundaryK)

theorem HomologyBoundaryCycle_append_cycle_closed {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (d_squared_zero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    {h k : BHist} :
    HomologyBoundaryCarrier d h -> HomologyCycleCarrier d k ->
      HomologyCycleCarrier d (append h k) := by
  intro boundaryH cycleK
  exact HomologyCycleCarrier_append_closed dAppend
    (HomologyBoundaryCarrier_cycle_closed d_squared_zero boundaryH) cycleK

theorem HomologyBoundaryCycle_append_hsame_transport {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dSquaredZero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    {h k r : BHist} :
    HomologyBoundaryCarrier d h -> HomologyCycleCarrier d k -> hsame (append h k) r ->
      HomologyCycleCarrier d r := by
  intro boundaryH cycleK sameResult
  exact hsame_trans (hsame_symm (dCongr sameResult))
    (HomologyBoundaryCycle_append_cycle_closed dAppend dSquaredZero boundaryH cycleK)

theorem HomologyCycleBoundary_append_hsame_transport {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dSquaredZero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    {h k r : BHist} :
    HomologyCycleCarrier d h -> HomologyBoundaryCarrier d k -> hsame (append h k) r ->
      HomologyCycleCarrier d r := by
  intro cycleH boundaryK sameResult
  exact hsame_trans (hsame_symm (dCongr sameResult))
    (HomologyCycleBoundary_append_cycle_closed dAppend dSquaredZero cycleH boundaryK)

theorem HomologyCycleBoundary_append_cycle_hsame_transport {d : BHist -> BHist}
    (dAppend : forall u v : BHist, hsame (d (append u v)) (append (d u) (d v)))
    (dCongr : forall {a b : BHist}, hsame a b -> hsame (d a) (d b))
    (dSquaredZero : forall u : BHist, hsame (d (d u)) BHist.Empty)
    {h k r : BHist} :
    HomologyCycleCarrier d h -> HomologyBoundaryCarrier d k -> hsame (append h k) r ->
      HomologyCycleCarrier d r := by
  intro cycleH boundaryK sameResult
  have cycleK : HomologyCycleCarrier d k :=
    HomologyBoundaryCarrier_cycle_of_d_squared_zero dCongr dSquaredZero boundaryK
  exact HomologyCycleCarrier_append_hsame_transport dAppend dCongr cycleH cycleK sameResult

end BEDC.Derived.HomologyUp
