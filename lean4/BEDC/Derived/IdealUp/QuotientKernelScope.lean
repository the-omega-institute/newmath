import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IdealZeroKernel_contained_in_whole_kernel
    {Carrier : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist} {sub : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    {x y : BHist} :
    (Carrier x ∧ Carrier y ∧ Carrier (sub x y) ∧ Classifier (sub x y) zero) ->
      Carrier x ∧ Carrier y := by
  intro kernelRows
  have _certified : NameCert Carrier Classifier := cert
  exact And.intro kernelRows.left kernelRows.right.left

theorem IdealZeroAndWholeQuotientKernel_scope
    {Carrier : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist} {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (negClosed : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (addClosed : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (zeroTransport :
      forall {x y : BHist}, Carrier x -> Carrier y -> Classifier x zero -> Classifier y zero) :
    (forall {x y : BHist},
        Carrier x -> Carrier y -> Carrier x ∧ Carrier y ∧ Carrier (add x (neg y))) ∧
      (forall {x y : BHist},
        Carrier x ∧ Carrier y ∧ Carrier (add x (neg y)) -> Carrier x ∧ Carrier y) := by
  have certifiedTransport :
      NameCert Carrier Classifier ∧
        (forall {x y : BHist}, Carrier x -> Carrier y -> Classifier x zero ->
          Classifier y zero) :=
    And.intro cert zeroTransport
  cases certifiedTransport with
  | intro _ _ =>
      constructor
      · intro x y carrierX carrierY
        exact And.intro carrierX (And.intro carrierY (addClosed carrierX (negClosed carrierY)))
      · intro x y kernelXY
        exact And.intro kernelXY.left kernelXY.right.left

theorem IdealQuotientKernel_product_difference_membership
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {add mul sub : BHist -> BHist -> BHist} {a a' b b' : BHist}
    (cert : NameCert Carrier Classifier)
    (idealAdd : forall {x y : BHist}, I x -> I y -> I (add x y))
    (idealTransport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (idealAbsorb :
      forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (productDifference :
      Classifier (add (mul (sub a a') b) (mul a' (sub b b')))
        (sub (mul a b) (mul a' b'))) :
    Carrier b -> Carrier a' -> I (sub a a') -> I (sub b b') ->
      I (sub (mul a b) (mul a' b')) := by
  intro carrierB carrierA' diffA diffB
  have _certified : NameCert Carrier Classifier := cert
  have rightAbsorbed : I (mul (sub a a') b) :=
    (idealAbsorb carrierB diffA).right
  have leftAbsorbed : I (mul a' (sub b b')) :=
    (idealAbsorb carrierA' diffB).left
  exact idealTransport (idealAdd rightAbsorbed leftAbsorbed) productDifference

theorem IdealWholePredicate_closure_rows
    {Carrier : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist} {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (zeroCarrier : Carrier zero)
    (addCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (negCarrier : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) :
    (forall {x : BHist}, Carrier x -> Carrier x) ∧
      Carrier zero ∧
      (forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y)) ∧
      (forall {x : BHist}, Carrier x -> Carrier (neg x)) ∧
      (forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) ∧
      (forall {x y : BHist}, Carrier x -> Classifier x y -> Carrier y) ∧
      (forall {r x : BHist},
        Carrier r -> Carrier x -> Carrier (mul r x) ∧ Carrier (mul x r)) := by
  constructor
  · intro _x carrierX
    exact carrierX
  · constructor
    · exact zeroCarrier
    · constructor
      · intro x y carrierX carrierY
        exact addCarrier carrierX carrierY
      · constructor
        · intro x carrierX
          exact negCarrier carrierX
        · constructor
          · intro x y carrierX carrierY
            exact mulCarrier carrierX carrierY
          · constructor
            · intro x y carrierX classifiedXY
              exact cert.carrier_respects_equiv classifiedXY carrierX
            · intro r x carrierR carrierX
              exact And.intro (mulCarrier carrierR carrierX) (mulCarrier carrierX carrierR)

theorem IdealSumQuotientKernel_diagonal_transport_scope
    {I J : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist} {add sub : BHist -> BHist -> BHist}
    (cert : NameCert (fun _ : BHist => True) Classifier)
    (I_zero : I zero) (J_zero : J zero)
    (zeroDecomp : Classifier (sub zero zero) (add zero zero))
    (subCongr :
      forall {x x' y y' : BHist},
        Classifier x x' -> Classifier y y' -> Classifier (sub x y) (sub x' y')) :
    (let K : BHist -> Prop :=
      fun z => exists u : BHist, exists v : BHist, I u ∧ J v ∧ Classifier z (add u v)
     K (sub zero zero) ∧
       forall {x y x' y' : BHist},
        Classifier x x' -> Classifier y y' -> K (sub x y) -> K (sub x' y')) := by
  constructor
  · exact Exists.intro zero
      (Exists.intro zero (And.intro I_zero (And.intro J_zero zeroDecomp)))
  · intro x y x' y' sameXX' sameYY' kernelXY
    cases kernelXY with
    | intro u kernelU =>
        cases kernelU with
        | intro v kernelV =>
            have sameSub :
                Classifier (sub x y) (sub x' y') :=
              subCongr sameXX' sameYY'
            have sameSubTarget :
                Classifier (sub x' y') (sub x y) :=
              NameCert.equiv_symm cert sameSub
            have sameTransport :
                Classifier (sub x' y') (add u v) :=
              NameCert.equiv_trans cert sameSubTarget kernelV.right.right
            exact Exists.intro u
              (Exists.intro v
                (And.intro kernelV.left (And.intro kernelV.right.left sameTransport)))

end BEDC.Derived.IdealUp
