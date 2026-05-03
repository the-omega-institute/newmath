import BEDC.Derived.MatrixUp
import BEDC.Derived.CommRingUp

namespace BEDC.Derived.DeterminantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.MatrixUp
open BEDC.Derived.CommRingUp

def DeterminantSingletonCertificate : Prop :=
  let DetReadback : BHist -> BHist := fun _ => BHist.Empty
  let DetCarrier : BHist -> Prop := fun M => MatrixSingletonCarrier M
  let DetClassifier : BHist -> BHist -> Prop := fun M N =>
    MatrixSingletonClassifier M N ∧
      CommRingSingletonClassifier (DetReadback M) (DetReadback N)
  SemanticNameCert DetCarrier DetCarrier DetCarrier DetClassifier ∧
    DetClassifier MatrixSingletonOne MatrixSingletonOne ∧
    (∀ {M N : BHist}, MatrixSingletonClassifier M N ->
      CommRingSingletonClassifier (DetReadback M) (DetReadback N)) ∧
    (∀ {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      CommRingSingletonClassifier (DetReadback (MatrixSingletonMul M N))
        (CommRingSingletonMul (DetReadback M) (DetReadback N)))

theorem DeterminantSingleton_semanticNameCert :
    SemanticNameCert
      (fun M : BHist => MatrixSingletonCarrier M)
      (fun M : BHist => MatrixSingletonCarrier M)
      (fun M : BHist => MatrixSingletonCarrier M)
      (fun M N : BHist =>
        MatrixSingletonClassifier M N ∧
          CommRingSingletonClassifier BHist.Empty BHist.Empty) := by
  have matrixCert :
      SemanticNameCert MatrixSingletonCarrier MatrixSingletonCarrier
        MatrixSingletonCarrier MatrixSingletonClassifier :=
    MatrixSingletonEmptyHistory_laws.left
  have emptyComm : CommRingSingletonClassifier BHist.Empty BHist.Empty := by
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  exact {
    core := {
      carrier_inhabited := matrixCert.core.carrier_inhabited
      equiv_refl := by
        intro M carrierM
        exact And.intro (matrixCert.core.equiv_refl carrierM) emptyComm
      equiv_symm := by
        intro M N sameMN
        exact And.intro (matrixCert.core.equiv_symm sameMN.left) emptyComm
      equiv_trans := by
        intro M N P sameMN sameNP
        exact And.intro (matrixCert.core.equiv_trans sameMN.left sameNP.left) emptyComm
      carrier_respects_equiv := by
        intro M N sameMN carrierM
        exact matrixCert.core.carrier_respects_equiv sameMN.left carrierM
    }
    pattern_sound := by
      intro M carrierM
      exact carrierM
    ledger_sound := by
      intro M carrierM
      exact carrierM
  }

end BEDC.Derived.DeterminantUp
