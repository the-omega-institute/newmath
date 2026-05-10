import BEDC.Derived.CompactMetricUp
import BEDC.Derived.ContinuousMapUp
import BEDC.FKernel.Bundle

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CompactMetricUp
open BEDC.Derived.ContinuousMapUp

structure SourceRows where
  source : BHist
  map : BHist
  target : BHist
  modulus : BHist
  cert : BHist
  distance : BHist
  eps : BHist
  bundle : ProbeBundle BHist
  stream : BHist -> BHist
  streamModulus : BHist -> BHist
  limit : BHist
  uniformPrecision : BHist
  uniformCert : BHist

def Pattern (s : SourceRows) : Prop :=
  ContinuousMapCarrier s.source s.map s.target s.modulus s.cert s.distance ∧
    CompactMetricCertificate (fun h : BHist => hsame h s.source) s.eps s.bundle
      s.stream s.streamModulus s.limit ∧
      UnaryHistory s.uniformPrecision ∧ Cont s.eps s.uniformPrecision s.uniformCert

def Classifier (s t : SourceRows) : Prop :=
  hsame s.source t.source ∧
    hsame s.map t.map ∧
      hsame s.target t.target ∧
        hsame s.modulus t.modulus ∧
          hsame s.cert t.cert ∧
            hsame s.distance t.distance ∧
              hsame s.eps t.eps ∧
                s.bundle = t.bundle ∧
                  (∀ n : BHist, UnaryHistory n -> hsame (s.stream n) (t.stream n)) ∧
                    (∀ n : BHist, UnaryHistory n ->
                      hsame (s.streamModulus n) (t.streamModulus n)) ∧
                      hsame s.limit t.limit ∧
                        hsame s.uniformPrecision t.uniformPrecision ∧
                          hsame s.uniformCert t.uniformCert

theorem stability {s t : SourceRows} :
    Pattern s -> Classifier s t -> Pattern t := by
  cases s with
  | mk source map target modulus cert distance eps bundle stream streamModulus limit
      uniformPrecision uniformCert =>
      cases t with
      | mk source' map' target' modulus' cert' distance' eps' bundle' stream'
          streamModulus' limit' uniformPrecision' uniformCert' =>
          intro pattern classifier
          cases pattern with
          | intro continuous rest =>
              cases rest with
              | intro compact rest =>
                  cases rest with
                  | intro precisionUnary uniformRow =>
                      cases classifier with
                      | intro sameSource classifierRest =>
                          cases sameSource
                          cases classifierRest with
                          | intro sameMap classifierRest =>
                              cases classifierRest with
                              | intro sameTarget classifierRest =>
                                  cases classifierRest with
                                  | intro sameModulus classifierRest =>
                                      cases classifierRest with
                                      | intro sameCert classifierRest =>
                                          cases classifierRest with
                                          | intro sameDistance classifierRest =>
                                              cases classifierRest with
                                              | intro sameEps classifierRest =>
                                                  cases classifierRest with
                                                  | intro sameBundle classifierRest =>
                                                      cases classifierRest with
                                                      | intro sameStream classifierRest =>
                                                          cases classifierRest with
                                                          | intro sameStreamModulus classifierRest =>
                                                              cases classifierRest with
                                                              | intro sameLimit classifierRest =>
                                                                  cases classifierRest with
                                                                  | intro samePrecision sameUniformCert =>
                                                                      constructor
                                                                      · cases sameMap
                                                                        cases sameTarget
                                                                        cases sameModulus
                                                                        cases sameCert
                                                                        cases sameDistance
                                                                        exact continuous
                                                                      · constructor
                                                                        · cases sameBundle
                                                                          exact CompactMetricCertificate_hsame_transport
                                                                            (fun {h k} sameHK carrier =>
                                                                              hsame_trans (hsame_symm sameHK)
                                                                                carrier)
                                                                            sameEps
                                                                            (fun {n} nUnary =>
                                                                              sameStream n nUnary)
                                                                            (fun {n} nUnary =>
                                                                              sameStreamModulus n nUnary)
                                                                            sameLimit compact
                                                                        · constructor
                                                                          · cases samePrecision
                                                                            exact precisionUnary
                                                                          · cases sameEps
                                                                            cases samePrecision
                                                                            cases sameUniformCert
                                                                            exact uniformRow

def Ledger : Type := SourceRows

end BEDC.Derived.CompactUniformContinuityUp
