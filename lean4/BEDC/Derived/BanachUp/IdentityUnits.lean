import BEDC.Derived.BanachUp

namespace BEDC.Derived.BanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem BanachSingletonBoundedLinearOperator_identity_unit_composites
    {T : BHist -> BHist} {K Lambda sourceIdLedger targetIdLedger : BHist} :
    BanachSingletonBoundedLinearOperator T K Lambda ->
      BanachSingletonBoundedLinearOperator (fun x : BHist => x) BHist.Empty sourceIdLedger ->
        BanachSingletonBoundedLinearOperator (fun x : BHist => x) BHist.Empty targetIdLedger ->
          BanachSingletonBoundedLinearOperator (fun x : BHist => T ((fun y : BHist => y) x))
              BHist.Empty (BHist.e0 (append Lambda sourceIdLedger)) ∧
            BanachSingletonBoundedLinearOperator (fun x : BHist => (fun y : BHist => y) (T x))
              BHist.Empty (BHist.e0 (append targetIdLedger Lambda)) ∧
              (forall {x : BHist}, BanachSingletonCarrier x ->
                BanachSingletonClassifier (T ((fun y : BHist => y) x)) (T x)) ∧
                (forall {x : BHist}, BanachSingletonCarrier x ->
                  BanachSingletonClassifier ((fun y : BHist => y) (T x)) (T x)) := by
  intro boundedT sourceIdentity targetIdentity
  have sourceComposite :
      BanachSingletonBoundedLinearOperator (fun x : BHist => T ((fun y : BHist => y) x))
        BHist.Empty (BHist.e0 (append Lambda sourceIdLedger)) :=
    BanachSingletonBoundedLinearOperator_composition_closure
      (T := fun x : BHist => x) (S := T) (K := BHist.Empty) (L := K)
      (Lambda := sourceIdLedger) (Gamma := Lambda) sourceIdentity boundedT
  have targetComposite :
      BanachSingletonBoundedLinearOperator (fun x : BHist => (fun y : BHist => y) (T x))
        BHist.Empty (BHist.e0 (append targetIdLedger Lambda)) :=
    BanachSingletonBoundedLinearOperator_composition_closure
      (T := T) (S := fun x : BHist => x) (K := K) (L := BHist.Empty)
      (Lambda := Lambda) (Gamma := targetIdLedger) boundedT targetIdentity
  exact And.intro sourceComposite
    (And.intro targetComposite
      (And.intro
        (fun {x : BHist} carrierX =>
          let targetCarrier := boundedT.right.right carrierX
          And.intro targetCarrier (And.intro targetCarrier (hsame_refl (T x))))
        (fun {x : BHist} carrierX =>
          let targetCarrier := boundedT.right.right carrierX
          And.intro targetCarrier (And.intro targetCarrier (hsame_refl (T x))))))

end BEDC.Derived.BanachUp
