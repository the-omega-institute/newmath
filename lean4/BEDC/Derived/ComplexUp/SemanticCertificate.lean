import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ComplexHistorySemanticCertificate_rat_pair_reflexive_witness :
    exists h real imag : BHist,
      RatUp.RatHistoryCarrier real ∧ RatUp.RatHistoryCarrier imag ∧ Cont real imag h ∧
        ComplexHistoryClassifier h h := by
  have cert := complex_history_semantic_name_certificate
  cases cert.core.carrier_inhabited with
  | intro h carrier =>
      cases carrier with
      | intro real rest =>
          cases rest with
          | intro imag data =>
              cases data with
              | intro realCarrier rest =>
                  cases rest with
                  | intro imagCarrier cont =>
                      have carrierH : ComplexHistoryCarrier h :=
                        Exists.intro real
                          (Exists.intro imag
                            (And.intro realCarrier (And.intro imagCarrier cont)))
                      have classified : ComplexHistoryClassifier h h :=
                        cert.core.equiv_refl carrierH
                      exact Exists.intro h
                        (Exists.intro real
                          (Exists.intro imag
                            (And.intro realCarrier
                              (And.intro imagCarrier (And.intro cont classified)))))

end BEDC.Derived.ComplexUp
