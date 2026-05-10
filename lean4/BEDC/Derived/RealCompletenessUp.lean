import BEDC.FKernel.Cont

namespace BEDC.Derived.RealCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

structure SourceRows where
  ratSource : BHist
  streamSource : BHist
  realSource : BHist
  cauchyWitness : BHist
  diagonalWitness : BHist
  stationaryWindow : BHist
  partitionSpine : BHist
  selectedTail : BHist
  completionCert : BHist
  uniquenessCert : BHist

def Pattern (s : SourceRows) : Prop :=
  Cont s.ratSource s.streamSource s.realSource ∧
    Cont s.realSource s.cauchyWitness s.diagonalWitness ∧
      Cont s.diagonalWitness s.stationaryWindow s.selectedTail ∧
        Cont s.selectedTail s.partitionSpine s.completionCert ∧
          Cont s.completionCert s.diagonalWitness s.uniquenessCert

def Classifier (s t : SourceRows) : Prop :=
  hsame s.ratSource t.ratSource ∧
    hsame s.streamSource t.streamSource ∧
      hsame s.realSource t.realSource ∧
        hsame s.cauchyWitness t.cauchyWitness ∧
          hsame s.diagonalWitness t.diagonalWitness ∧
            hsame s.stationaryWindow t.stationaryWindow ∧
              hsame s.partitionSpine t.partitionSpine ∧
                hsame s.selectedTail t.selectedTail ∧
                  hsame s.completionCert t.completionCert ∧
                    hsame s.uniquenessCert t.uniquenessCert

theorem stability {s t : SourceRows} :
    Pattern s -> Classifier s t -> Pattern t := by
  cases s with
  | mk ratSource streamSource realSource cauchyWitness diagonalWitness
      stationaryWindow partitionSpine selectedTail completionCert uniquenessCert =>
      cases t with
      | mk ratSource' streamSource' realSource' cauchyWitness' diagonalWitness'
          stationaryWindow' partitionSpine' selectedTail' completionCert'
          uniquenessCert' =>
          intro pattern classified
          unfold Pattern at pattern ⊢
          unfold Classifier at classified
          cases classified with
          | intro sameRat rest =>
              cases rest with
              | intro sameStream rest =>
                  cases rest with
                  | intro sameReal rest =>
                      cases rest with
                      | intro sameCauchy rest =>
                          cases rest with
                          | intro sameDiagonal rest =>
                              cases rest with
                              | intro sameStationary rest =>
                                  cases rest with
                                  | intro samePartition rest =>
                                      cases rest with
                                      | intro sameTail rest =>
                                          cases rest with
                                          | intro sameCompletion sameUnique =>
                                              cases sameRat
                                              cases sameStream
                                              cases sameReal
                                              cases sameCauchy
                                              cases sameDiagonal
                                              cases sameStationary
                                              cases samePartition
                                              cases sameTail
                                              cases sameCompletion
                                              cases sameUnique
                                              exact pattern

structure LedgerRow where
  source : SourceRows
  rawRatSeed : BHist
  rawStreamSeed : BHist
  rawRealSeal : BHist
  rawModulusTrace : BHist
  rawDiagonalTrace : BHist
  rawWindowTrace : BHist
  rawPartitionTrace : BHist

def Ledger : Type := LedgerRow

end BEDC.Derived.RealCompletenessUp
