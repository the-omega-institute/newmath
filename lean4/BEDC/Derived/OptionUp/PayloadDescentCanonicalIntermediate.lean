import BEDC.Derived.OptionUp.PayloadDescent

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionMapRel_composite_factorization_canonical_intermediate
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (rhoE : forall b : BHist, T b -> U (epsilon.map b))
    (delta_hsame :
      forall x y : BHist, S x -> S y -> hsame x y -> hsame (delta.map x) (delta.map y))
    (epsilon_hsame :
      forall x y : BHist, T x -> T y -> hsame x y ->
        hsame (epsilon.map x) (epsilon.map y))
    {h k k' m : BHist} :
    (TaggedOptionMapRel S T delta h k ∧ TaggedOptionMapRel T U epsilon k m) ->
      (TaggedOptionMapRel S T delta h k' ∧ TaggedOptionMapRel T U epsilon k' m) ->
        (hsame h BHist.Empty ∧ hsame k BHist.Empty ∧ hsame k' BHist.Empty ∧
            hsame m BHist.Empty) ∨
          (exists a : BHist,
            S a ∧ T (delta.map a) ∧ U (epsilon.map (delta.map a)) ∧
              hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 (delta.map a)) ∧
                hsame k' (BHist.e1 (delta.map a)) ∧
                  hsame m (BHist.e1 (epsilon.map (delta.map a)))) := by
  intro first second
  cases first with
  | intro deltaRel epsilonRel =>
      cases second with
      | intro deltaRel' epsilonRel' =>
          cases deltaRel with
          | inl deltaAbsent =>
              cases epsilonRel with
              | inl epsilonAbsent =>
                  cases deltaRel' with
                  | inl deltaAbsent' =>
                      cases epsilonRel' with
                      | inl _epsilonAbsent' =>
                          exact Or.inl
                            ⟨deltaAbsent.left, deltaAbsent.right, deltaAbsent'.right,
                              epsilonAbsent.right⟩
                      | inr epsilonPresent' =>
                          cases epsilonPresent' with
                          | intro b dataE' =>
                              exact False.elim
                                (not_hsame_e1_empty
                                  (hsame_trans (hsame_symm dataE'.right.right.left)
                                    deltaAbsent'.right))
                  | inr deltaPresent' =>
                      cases deltaPresent' with
                      | intro a dataD' =>
                          exact False.elim
                            (not_hsame_emp_e1
                              (hsame_trans (hsame_symm deltaAbsent.left)
                                dataD'.right.right.left))
              | inr epsilonPresent =>
                  cases epsilonPresent with
                  | intro b dataE =>
                      exact False.elim
                        (not_hsame_e1_empty
                          (hsame_trans (hsame_symm dataE.right.right.left)
                            deltaAbsent.right))
          | inr deltaPresent =>
              cases deltaPresent with
              | intro a dataD =>
                  cases dataD with
                  | intro sourceA restD =>
                      cases restD with
                      | intro _targetDeltaA restD =>
                          cases restD with
                          | intro sameHPresent sameKDelta =>
                              have targetDeltaCanonical : T (delta.map a) :=
                                rhoD a sourceA
                              cases epsilonRel with
                              | inl epsilonAbsent =>
                                  exact False.elim
                                    (not_hsame_e1_empty
                                      (hsame_trans (hsame_symm sameKDelta)
                                        epsilonAbsent.left))
                              | inr epsilonPresent =>
                                  cases epsilonPresent with
                                  | intro b dataE =>
                                      cases dataE with
                                      | intro targetB restE =>
                                          cases restE with
                                          | intro _targetEpsilonB restE =>
                                              cases restE with
                                              | intro sameKB sameMPresent =>
                                                  have sameDeltaB : hsame (delta.map a) b :=
                                                    hsame_e1_iff.mp
                                                      (hsame_trans (hsame_symm sameKDelta)
                                                        sameKB)
                                                  have sameEpsilonB :
                                                      hsame (epsilon.map (delta.map a))
                                                        (epsilon.map b) :=
                                                    epsilon_hsame (delta.map a) b
                                                      targetDeltaCanonical targetB sameDeltaB
                                                  have targetEpsilonCanonical :
                                                      U (epsilon.map (delta.map a)) :=
                                                    rhoE (delta.map a) targetDeltaCanonical
                                                  have sameMCanonical :
                                                      hsame m
                                                        (BHist.e1
                                                          (epsilon.map (delta.map a))) :=
                                                    hsame_trans sameMPresent
                                                      (hsame_e1_congr (hsame_symm sameEpsilonB))
                                                  cases deltaRel' with
                                                  | inl deltaAbsent' =>
                                                      exact False.elim
                                                        (not_hsame_emp_e1
                                                          (hsame_trans
                                                            (hsame_symm deltaAbsent'.left)
                                                            sameHPresent))
                                                  | inr deltaPresent' =>
                                                      cases deltaPresent' with
                                                      | intro a' dataD' =>
                                                          cases dataD' with
                                                          | intro sourceA' restD' =>
                                                              cases restD' with
                                                              | intro _targetDeltaA' restD' =>
                                                                  cases restD' with
                                                                  | intro sameHPresent'
                                                                      sameK'Delta' =>
                                                                      have sameAA' :
                                                                          hsame a a' :=
                                                                        hsame_e1_iff.mp
                                                                          (hsame_trans
                                                                            (hsame_symm
                                                                              sameHPresent)
                                                                            sameHPresent')
                                                                      have sameDeltaAA' :
                                                                          hsame (delta.map a)
                                                                            (delta.map a') :=
                                                                        delta_hsame a a' sourceA sourceA'
                                                                          sameAA'
                                                                      have sameK'Canonical :
                                                                          hsame k'
                                                                            (BHist.e1
                                                                              (delta.map a)) :=
                                                                        hsame_trans sameK'Delta'
                                                                          (hsame_e1_congr
                                                                            (hsame_symm
                                                                              sameDeltaAA'))
                                                                      cases epsilonRel' with
                                                                      | inl epsilonAbsent' =>
                                                                          exact False.elim
                                                                            (not_hsame_e1_empty
                                                                              (hsame_trans
                                                                                (hsame_symm
                                                                                  sameK'Canonical)
                                                                                epsilonAbsent'.left))
                                                                      | inr _epsilonPresent' =>
                                                                          exact Or.inr
                                                                            ⟨a, sourceA,
                                                                              targetDeltaCanonical,
                                                                              targetEpsilonCanonical,
                                                                              sameHPresent,
                                                                              sameKDelta,
                                                                              sameK'Canonical,
                                                                              sameMCanonical⟩

end BEDC.Derived.OptionUp
