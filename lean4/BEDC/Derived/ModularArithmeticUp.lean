import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModularArithmeticUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModularArithmeticResidueSource [AskSetup] [PackageSetup]
    (modulus witness representative residueLedger pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory modulus ∧ PositiveUnaryDenominator witness ∧ UnaryHistory representative ∧
    Cont modulus witness residueLedger ∧ Cont residueLedger representative pkgrow ∧
      PkgSig bundle pkgrow pkg

theorem ModularArithmeticResidueSource_carrier_stability [AskSetup] [PackageSetup]
    {modulus witness representative residueLedger pkgrow modulus' witness' representative'
      residueLedger' pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueSource modulus witness representative residueLedger pkgrow bundle
        pkg ->
      hsame modulus modulus' ->
        hsame witness witness' ->
          hsame representative representative' ->
            Cont modulus' witness' residueLedger' ->
              Cont residueLedger' representative' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  ModularArithmeticResidueSource modulus' witness' representative'
                      residueLedger' pkgrow' bundle pkg ∧
                    hsame residueLedger residueLedger' ∧ hsame pkgrow pkgrow' := by
  intro source sameModulus sameWitness sameRepresentative residueLedgerRow' pkgrowRow' pkgrowSig'
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport source.left sameModulus
  have witnessPositive' : PositiveUnaryDenominator witness' :=
    PositiveUnaryDenominator_hsame_transport sameWitness source.right.left
  have representativeUnary' : UnaryHistory representative' :=
    unary_transport source.right.right.left sameRepresentative
  have sameResidueLedger : hsame residueLedger residueLedger' :=
    cont_respects_hsame sameModulus sameWitness source.right.right.right.left residueLedgerRow'
  have samePkgrow : hsame pkgrow pkgrow' :=
    cont_respects_hsame sameResidueLedger sameRepresentative
      source.right.right.right.right.left pkgrowRow'
  exact And.intro
    (And.intro modulusUnary'
      (And.intro witnessPositive'
        (And.intro representativeUnary'
          (And.intro residueLedgerRow' (And.intro pkgrowRow' pkgrowSig')))))
    (And.intro sameResidueLedger samePkgrow)

end BEDC.Derived.ModularArithmeticUp
