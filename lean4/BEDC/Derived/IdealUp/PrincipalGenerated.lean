import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive IdealPrincipalGenerated
    (Carrier : BHist -> Prop) (Classifier : BHist -> BHist -> Prop)
    (cert : NameCert Carrier Classifier) (zero generator : BHist)
    (add mul : BHist -> BHist -> BHist) (neg : BHist -> BHist) : BHist -> Prop where
  | zero :
      Carrier zero ->
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg zero
  | monomial :
      forall {l r : BHist},
        Carrier l -> Carrier r ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg
            (mul (mul l generator) r)
  | add :
      forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (add x y)
  | neg :
      forall {x : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (neg x)
  | transport :
      forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          Classifier x y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y

theorem IdealPrincipalGenerated_subtractive_closure_rows
    {Carrier : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero generator : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (zeroCarrier : Carrier zero)
    (generatorCarrier : Carrier generator)
    (addCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (negCarrier : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) :
    (forall {x : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x -> Carrier x) ∧
      IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg zero ∧
      (forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (add x y)) ∧
      (forall {x : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (neg x)) ∧
      (forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          Classifier x y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y) := by
  let Generated :=
    IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg
  have support : forall {x : BHist}, Generated x -> Carrier x := by
    intro x memberX
    induction memberX with
    | zero _ =>
        exact zeroCarrier
    | monomial carrierL carrierR =>
        exact mulCarrier (mulCarrier carrierL generatorCarrier) carrierR
    | add _left _right leftSupport rightSupport =>
        exact addCarrier leftSupport rightSupport
    | neg _member supportX =>
        exact negCarrier supportX
    | transport _member classified supportX =>
        exact NameCert.carrier_respects_equiv cert classified supportX
  constructor
  · intro x memberX
    exact support memberX
  · constructor
    · exact IdealPrincipalGenerated.zero zeroCarrier
    · constructor
      · intro x y memberX memberY
        exact IdealPrincipalGenerated.add memberX memberY
      · constructor
        · intro x memberX
          exact IdealPrincipalGenerated.neg memberX
        · intro x y memberX classifiedXY
          exact IdealPrincipalGenerated.transport memberX classifiedXY

theorem IdealPrincipalGenerated_absorption_closure_rows
    {Carrier : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero generator : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (zeroCarrier : Carrier zero)
    (generatorCarrier : Carrier generator)
    (addCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (negCarrier : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (mulZeroLeft : forall {r : BHist}, Carrier r -> Classifier (mul r zero) zero)
    (mulZeroRight : forall {r : BHist}, Carrier r -> Classifier (mul zero r) zero)
    (mulAssocLeft :
      forall {t l r : BHist},
        Carrier t -> Carrier l -> Carrier r ->
          Classifier (mul t (mul (mul l generator) r))
            (mul (mul (mul t l) generator) r))
    (mulAssocRight :
      forall {t l r : BHist},
        Carrier t -> Carrier l -> Carrier r ->
          Classifier (mul (mul (mul l generator) r) t)
            (mul (mul l generator) (mul r t)))
    (mulAddLeft :
      forall {t x y : BHist},
        Carrier t -> Carrier x -> Carrier y ->
          Classifier (mul t (add x y)) (add (mul t x) (mul t y)))
    (mulAddRight :
      forall {t x y : BHist},
        Carrier t -> Carrier x -> Carrier y ->
          Classifier (mul (add x y) t) (add (mul x t) (mul y t)))
    (mulNegLeft :
      forall {t x : BHist},
        Carrier t -> Carrier x -> Classifier (mul t (neg x)) (neg (mul t x)))
    (mulNegRight :
      forall {t x : BHist},
        Carrier t -> Carrier x -> Classifier (mul (neg x) t) (neg (mul x t)))
    (mulCongrLeft :
      forall {t x y : BHist},
        Carrier t -> Classifier x y -> Classifier (mul t x) (mul t y))
    (mulCongrRight :
      forall {t x y : BHist},
        Carrier t -> Classifier x y -> Classifier (mul x t) (mul y t)) :
    (forall {t x : BHist},
        Carrier t ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg
              (mul t x) ∧
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg
              (mul x t)) ∧
      (forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg
              (mul x y)) := by
  let Generated :=
    IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg
  have support : forall {x : BHist}, Generated x -> Carrier x := by
    intro x memberX
    induction memberX with
    | zero _ =>
        exact zeroCarrier
    | monomial carrierL carrierR =>
        exact mulCarrier (mulCarrier carrierL generatorCarrier) carrierR
    | add left right leftSupport rightSupport =>
        exact addCarrier leftSupport rightSupport
    | neg member supportX =>
        exact negCarrier supportX
    | transport member classified supportX =>
        exact NameCert.carrier_respects_equiv cert classified supportX
  have absorb :
      forall {t x : BHist}, Carrier t -> Generated x ->
        Generated (mul t x) ∧ Generated (mul x t) := by
    intro t x carrierT memberX
    induction memberX with
    | zero _ =>
        have zeroMember : Generated zero :=
          IdealPrincipalGenerated.zero zeroCarrier
        exact
          ⟨IdealPrincipalGenerated.transport zeroMember
              (NameCert.equiv_symm cert (mulZeroLeft carrierT)),
            IdealPrincipalGenerated.transport zeroMember
              (NameCert.equiv_symm cert (mulZeroRight carrierT))⟩
    | monomial carrierL carrierR =>
        rename_i l r
        have carrierTL : Carrier (mul t l) := mulCarrier carrierT carrierL
        have carrierRT : Carrier (mul r t) := mulCarrier carrierR carrierT
        have leftMonomial : Generated (mul (mul (mul t l) generator) r) :=
          IdealPrincipalGenerated.monomial carrierTL carrierR
        have rightMonomial : Generated (mul (mul l generator) (mul r t)) :=
          IdealPrincipalGenerated.monomial carrierL carrierRT
        exact
          ⟨IdealPrincipalGenerated.transport leftMonomial
              (NameCert.equiv_symm cert (mulAssocLeft carrierT carrierL carrierR)),
            IdealPrincipalGenerated.transport rightMonomial
              (NameCert.equiv_symm cert (mulAssocRight carrierT carrierL carrierR))⟩
    | add memberX memberY absorbX absorbY =>
        rename_i x y
        have carrierX : Carrier x := support memberX
        have carrierY : Carrier y := support memberY
        have leftSum : Generated (add (mul t x) (mul t y)) :=
          IdealPrincipalGenerated.add absorbX.left absorbY.left
        have rightSum : Generated (add (mul x t) (mul y t)) :=
          IdealPrincipalGenerated.add absorbX.right absorbY.right
        exact
          ⟨IdealPrincipalGenerated.transport leftSum
              (NameCert.equiv_symm cert (mulAddLeft carrierT carrierX carrierY)),
            IdealPrincipalGenerated.transport rightSum
              (NameCert.equiv_symm cert (mulAddRight carrierT carrierX carrierY))⟩
    | neg memberX absorbX =>
        rename_i x
        have carrierX : Carrier x := support memberX
        have leftNeg : Generated (neg (mul t x)) :=
          IdealPrincipalGenerated.neg absorbX.left
        have rightNeg : Generated (neg (mul x t)) :=
          IdealPrincipalGenerated.neg absorbX.right
        exact
          ⟨IdealPrincipalGenerated.transport leftNeg
              (NameCert.equiv_symm cert (mulNegLeft carrierT carrierX)),
            IdealPrincipalGenerated.transport rightNeg
              (NameCert.equiv_symm cert (mulNegRight carrierT carrierX))⟩
    | transport memberX classifiedXY absorbX =>
        rename_i x y
        exact
          ⟨IdealPrincipalGenerated.transport absorbX.left
              (mulCongrLeft carrierT classifiedXY),
            IdealPrincipalGenerated.transport absorbX.right
              (mulCongrRight carrierT classifiedXY)⟩
  constructor
  · intro t x carrierT memberX
    exact absorb carrierT memberX
  · intro x y memberX memberY
    exact (absorb (support memberY) memberX).right

theorem IdealPrincipalGenerated_full_ideal_closure_rows
    {Carrier : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero generator : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (zeroCarrier : Carrier zero)
    (generatorCarrier : Carrier generator)
    (addCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (negCarrier : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (mulZeroLeft : forall {r : BHist}, Carrier r -> Classifier (mul r zero) zero)
    (mulZeroRight : forall {r : BHist}, Carrier r -> Classifier (mul zero r) zero)
    (mulAssocLeft :
      forall {t l r : BHist},
        Carrier t -> Carrier l -> Carrier r ->
          Classifier (mul t (mul (mul l generator) r))
            (mul (mul (mul t l) generator) r))
    (mulAssocRight :
      forall {t l r : BHist},
        Carrier t -> Carrier l -> Carrier r ->
          Classifier (mul (mul (mul l generator) r) t)
            (mul (mul l generator) (mul r t)))
    (mulAddLeft :
      forall {t x y : BHist},
        Carrier t -> Carrier x -> Carrier y ->
          Classifier (mul t (add x y)) (add (mul t x) (mul t y)))
    (mulAddRight :
      forall {t x y : BHist},
        Carrier t -> Carrier x -> Carrier y ->
          Classifier (mul (add x y) t) (add (mul x t) (mul y t)))
    (mulNegLeft :
      forall {t x : BHist},
        Carrier t -> Carrier x -> Classifier (mul t (neg x)) (neg (mul t x)))
    (mulNegRight :
      forall {t x : BHist},
        Carrier t -> Carrier x -> Classifier (mul (neg x) t) (neg (mul x t)))
    (mulCongrLeft :
      forall {t x y : BHist},
        Carrier t -> Classifier x y -> Classifier (mul t x) (mul t y))
    (mulCongrRight :
      forall {t x y : BHist},
        Carrier t -> Classifier x y -> Classifier (mul x t) (mul y t)) :
    (forall {x : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x -> Carrier x) ∧
      IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg zero ∧
      (forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (add x y)) ∧
      (forall {x : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (neg x)) ∧
      (forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (mul x y)) ∧
      (forall {x y : BHist},
        IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
          Classifier x y ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg y) ∧
      (forall {r x : BHist},
        Carrier r ->
          IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg x ->
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (mul r x) ∧
            IdealPrincipalGenerated Carrier Classifier cert zero generator add mul neg (mul x r)) := by
  have subtractive :=
    IdealPrincipalGenerated_subtractive_closure_rows (cert := cert)
      (zeroCarrier := zeroCarrier) (generatorCarrier := generatorCarrier)
      (addCarrier := addCarrier) (negCarrier := negCarrier) (mulCarrier := mulCarrier)
  have absorption :=
    IdealPrincipalGenerated_absorption_closure_rows (cert := cert)
      (zeroCarrier := zeroCarrier) (generatorCarrier := generatorCarrier)
      (addCarrier := addCarrier) (negCarrier := negCarrier) (mulCarrier := mulCarrier)
      (mulZeroLeft := mulZeroLeft) (mulZeroRight := mulZeroRight)
      (mulAssocLeft := mulAssocLeft) (mulAssocRight := mulAssocRight)
      (mulAddLeft := mulAddLeft) (mulAddRight := mulAddRight)
      (mulNegLeft := mulNegLeft) (mulNegRight := mulNegRight)
      (mulCongrLeft := mulCongrLeft) (mulCongrRight := mulCongrRight)
  exact
    ⟨subtractive.left,
      subtractive.right.left,
      subtractive.right.right.left,
      subtractive.right.right.right.left,
      absorption.right,
      subtractive.right.right.right.right,
      absorption.left⟩

end BEDC.Derived.IdealUp
