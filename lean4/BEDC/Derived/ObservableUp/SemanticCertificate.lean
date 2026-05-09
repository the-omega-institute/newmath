import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ObservableBHistOperatorCarrier_semanticNameCert [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      SemanticNameCert
        (fun e : BHist =>
          ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance
            ledger e bundle pkg)
        (fun e : BHist =>
          ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance
            ledger e bundle pkg)
        (fun e : BHist =>
          ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance
            ledger e bundle pkg)
        (fun e e' : BHist =>
          ObservableSpectralExpectationClassifier hilbert operator spectrum expectation witness
            provenance ledger e hilbert operator spectrum expectation witness provenance ledger e'
            bundle pkg) := by
  intro carrier
  have core :
      NameCert
        (fun e : BHist =>
          ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance
            ledger e bundle pkg)
        (fun e e' : BHist =>
          ObservableSpectralExpectationClassifier hilbert operator spectrum expectation witness
            provenance ledger e hilbert operator spectrum expectation witness provenance ledger e'
            bundle pkg) := {
    carrier_inhabited := Exists.intro endpoint carrier
    equiv_refl := by
      intro e carrierE
      exact And.intro carrierE
        (And.intro carrierE
          (And.intro (hsame_refl hilbert)
            (And.intro (hsame_refl operator)
              (And.intro (hsame_refl spectrum)
                (And.intro (hsame_refl expectation)
                  (And.intro (hsame_refl witness)
                    (And.intro (hsame_refl provenance)
                      (And.intro (hsame_refl ledger) (hsame_refl e)))))))))
    equiv_symm := by
      intro e e' classified
      exact And.intro classified.right.left
        (And.intro classified.left
          (And.intro (hsame_symm classified.right.right.left)
            (And.intro (hsame_symm classified.right.right.right.left)
              (And.intro (hsame_symm classified.right.right.right.right.left)
                (And.intro (hsame_symm classified.right.right.right.right.right.left)
                  (And.intro (hsame_symm classified.right.right.right.right.right.right.left)
                    (And.intro (hsame_symm classified.right.right.right.right.right.right.right.left)
                      (And.intro
                        (hsame_symm classified.right.right.right.right.right.right.right.right.left)
                        (hsame_symm
                          classified.right.right.right.right.right.right.right.right.right)))))))))
    equiv_trans := by
      intro e e' e'' classifiedEE' classifiedE'E''
      have endpointSame : hsame e e'' :=
        hsame_trans classifiedEE'.right.right.right.right.right.right.right.right.right
          classifiedE'E''.right.right.right.right.right.right.right.right.right
      exact And.intro classifiedEE'.left
        (And.intro classifiedE'E''.right.left
          (And.intro (hsame_refl hilbert)
            (And.intro (hsame_refl operator)
              (And.intro (hsame_refl spectrum)
                (And.intro (hsame_refl expectation)
                  (And.intro (hsame_refl witness)
                    (And.intro (hsame_refl provenance)
                      (And.intro (hsame_refl ledger) endpointSame))))))))
    carrier_respects_equiv := by
      intro e e' classified _carrierE
      exact classified.right.left
  }
  exact {
    core := core
    pattern_sound := by
      intro e carrierE
      exact carrierE
    ledger_sound := by
      intro e carrierE
      exact carrierE
  }

end BEDC.Derived.ObservableUp
