import BEDC.Derived.RealityConstrainedSynthesisSealUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedSynthesisSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedSynthesisSeal_independence_boundary
    (x : RealityConstrainedSynthesisSealUp) :
    Exists fun audit : BHist =>
      Exists fun fit : BHist =>
        Exists fun objectivity : BHist =>
          Exists fun observation : BHist =>
            Exists fun explanation : BHist =>
              Exists fun tower : BHist =>
                Exists fun ledger : BHist =>
                  Exists fun failure : BHist =>
                    Exists fun transport : BHist =>
                      Exists fun replay : BHist =>
                        Exists fun provenance : BHist =>
                          Exists fun name : BHist =>
                            Exists fun auditFit : BHist =>
                              Exists fun fitObjectivity : BHist =>
                                Exists fun objectivityObservation : BHist =>
                                  Exists fun towerLedger : BHist =>
                                    Exists fun failureReplay : BHist =>
                                      Exists fun finalName : BHist =>
                                        x =
                                            RealityConstrainedSynthesisSealUp.mk audit fit
                                              objectivity observation explanation tower ledger
                                              failure transport replay provenance name ∧
                                          realityConstrainedSynthesisSealFields x =
                                            [audit, fit, objectivity, observation, explanation,
                                              tower, ledger, failure, transport, replay,
                                              provenance, name] ∧
                                            Cont audit fit auditFit ∧
                                              Cont fit objectivity fitObjectivity ∧
                                                Cont objectivity observation
                                                    objectivityObservation ∧
                                                  Cont tower ledger towerLedger ∧
                                                    Cont failure replay failureReplay ∧
                                                      Cont provenance name finalName ∧
                                                        hsame finalName
                                                          (append provenance name) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk audit fit objectivity observation explanation tower ledger failure transport replay
      provenance name =>
      exact
        Exists.intro audit
          (Exists.intro fit
            (Exists.intro objectivity
              (Exists.intro observation
                (Exists.intro explanation
                  (Exists.intro tower
                    (Exists.intro ledger
                      (Exists.intro failure
                        (Exists.intro transport
                          (Exists.intro replay
                            (Exists.intro provenance
                              (Exists.intro name
                                (Exists.intro (append audit fit)
                                  (Exists.intro (append fit objectivity)
                                    (Exists.intro (append objectivity observation)
                                      (Exists.intro (append tower ledger)
                                        (Exists.intro (append failure replay)
                                          (Exists.intro (append provenance name)
                                            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                                              rfl⟩)))))))))))))))))

end BEDC.Derived.RealityConstrainedSynthesisSealUp
