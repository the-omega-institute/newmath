import BEDC.Derived.DomainTruthCertificateUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.DomainTruthCertificateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem DomainTruthCertificateUp_sibling_independence
    (x : DomainTruthCertificateUp) :
    ∃ truth domain openFit observerInvariant continuation failure transport replay provenance
        package localName domainOpenFit failureLocal : BHist,
      x =
          DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation failure
            transport replay provenance package localName ∧
        Cont domain openFit domainOpenFit ∧
          Cont failure localName failureLocal ∧
            List.Mem (domainTruthCertificateEncodeBHist domain)
              (domainTruthCertificateToEventFlow x) ∧
              List.Mem (domainTruthCertificateEncodeBHist openFit)
                (domainTruthCertificateToEventFlow x) ∧
                List.Mem (domainTruthCertificateEncodeBHist observerInvariant)
                  (domainTruthCertificateToEventFlow x) ∧
                  List.Mem (domainTruthCertificateEncodeBHist failure)
                    (domainTruthCertificateToEventFlow x) := by
  -- BEDC touchpoint anchor: BHist BMark Cont List.Mem
  cases x with
  | mk truth domain openFit observerInvariant continuation failure transport replay provenance
      package localName =>
      have domainListed :
          List.Mem (domainTruthCertificateEncodeBHist domain)
            (domainTruthCertificateToEventFlow
              (DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation
                failure transport replay provenance package localName)) := by
        change
          List.Mem (domainTruthCertificateEncodeBHist domain)
            [[BMark.b0], domainTruthCertificateEncodeBHist truth, [BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist domain, [BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist openFit,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist observerInvariant,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist continuation,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist failure,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              domainTruthCertificateEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist replay,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist package,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist localName]
        exact
          List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))
      have openFitListed :
          List.Mem (domainTruthCertificateEncodeBHist openFit)
            (domainTruthCertificateToEventFlow
              (DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation
                failure transport replay provenance package localName)) := by
        change
          List.Mem (domainTruthCertificateEncodeBHist openFit)
            [[BMark.b0], domainTruthCertificateEncodeBHist truth, [BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist domain, [BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist openFit,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist observerInvariant,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist continuation,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist failure,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              domainTruthCertificateEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist replay,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist package,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist localName]
        exact
          List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self))))
      have observerListed :
          List.Mem (domainTruthCertificateEncodeBHist observerInvariant)
            (domainTruthCertificateToEventFlow
              (DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation
                failure transport replay provenance package localName)) := by
        change
          List.Mem (domainTruthCertificateEncodeBHist observerInvariant)
            [[BMark.b0], domainTruthCertificateEncodeBHist truth, [BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist domain, [BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist openFit,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist observerInvariant,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist continuation,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist failure,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              domainTruthCertificateEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist replay,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist package,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist localName]
        exact
          List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))))))
      have failureListed :
          List.Mem (domainTruthCertificateEncodeBHist failure)
            (domainTruthCertificateToEventFlow
              (DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation
                failure transport replay provenance package localName)) := by
        change
          List.Mem (domainTruthCertificateEncodeBHist failure)
            [[BMark.b0], domainTruthCertificateEncodeBHist truth, [BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist domain, [BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist openFit,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist observerInvariant,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist continuation,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist failure,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              domainTruthCertificateEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist replay,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist package,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              domainTruthCertificateEncodeBHist localName]
        exact
          List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
      exact
        ⟨truth, domain, openFit, observerInvariant, continuation, failure, transport, replay,
          provenance, package, localName, append domain openFit, append failure localName,
          rfl, rfl, rfl, domainListed, openFitListed, observerListed, failureListed⟩

end BEDC.Derived.DomainTruthCertificateUp
