import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.CofibrantReplacementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def CofibrantReplacementBHistSource [AskSetup] [PackageSetup]
    (object cofibrant arrow factorization lifting pkgrow ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont object cofibrant arrow ∧ Cont arrow factorization lifting ∧
    Cont lifting pkgrow ledger ∧ PkgSig bundle pkgrow pkg

theorem CofibrantReplacementBHistSource_factorization_transport [AskSetup] [PackageSetup]
    {object cofibrant arrow factorization lifting pkgrow ledger object' cofibrant' arrow'
      factorization' lifting' pkgrow' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofibrantReplacementBHistSource object cofibrant arrow factorization lifting pkgrow ledger
        bundle pkg ->
      hsame object object' ->
        hsame cofibrant cofibrant' ->
          hsame factorization factorization' ->
            hsame pkgrow pkgrow' ->
              Cont object' cofibrant' arrow' ->
                Cont arrow' factorization' lifting' ->
                  Cont lifting' pkgrow' ledger' ->
                    PkgSig bundle pkgrow' pkg ->
                      CofibrantReplacementBHistSource object' cofibrant' arrow' factorization'
                          lifting' pkgrow' ledger' bundle pkg ∧
                        hsame arrow arrow' ∧ hsame lifting lifting' ∧ hsame ledger ledger' := by
  intro source sameObject sameCofibrant sameFactorization samePkgrow
  intro targetObject targetFactorization targetPkg targetPkgSig
  have sameArrow : hsame arrow arrow' :=
    cont_respects_hsame sameObject sameCofibrant source.left targetObject
  have sameLifting : hsame lifting lifting' :=
    cont_respects_hsame sameArrow sameFactorization source.right.left targetFactorization
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLifting samePkgrow source.right.right.left targetPkg
  exact
    And.intro
      (And.intro targetObject
        (And.intro targetFactorization (And.intro targetPkg targetPkgSig)))
      (And.intro sameArrow (And.intro sameLifting sameLedger))

end BEDC.Derived.CofibrantReplacementUp
