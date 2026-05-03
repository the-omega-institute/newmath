import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.Derived.MatrixUp
import BEDC.Derived.CommRingUp

namespace BEDC.Derived.DeterminantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

def DeterminantSingletonReadback (_M : BHist) : BHist :=
  BHist.Empty

def DeterminantSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def DeterminantSingletonClassifier (h k : BHist) : Prop :=
  DeterminantSingletonCarrier h ∧ DeterminantSingletonCarrier k ∧ hsame h k

def DeterminantSingletonDet (M : BHist) : BHist :=
  append M BHist.Empty

def DeterminantSingletonEndpointEmpty (M r : BHist) : Prop :=
  MatrixUp.MatrixSingletonClassifier M BHist.Empty ∧
    CommRingUp.CommRingSingletonClassifier r BHist.Empty

def DeterminantSingletonEndpoint (M r : BHist) : Prop :=
  DeterminantSingletonEndpointEmpty M r ∧
    MatrixSingletonCarrier M ∧ CommRingSingletonClassifier r CommRingSingletonOne

theorem DeterminantSingleton_certificate :
    SemanticNameCert DeterminantSingletonCarrier DeterminantSingletonCarrier
      DeterminantSingletonCarrier DeterminantSingletonClassifier ∧
      (forall {M r : BHist}, DeterminantSingletonEndpoint M r <->
        MatrixSingletonCarrier M ∧ CommRingSingletonClassifier r CommRingSingletonOne) ∧
      CommRingSingletonClassifier (DeterminantSingletonDet MatrixSingletonOne)
        CommRingSingletonOne ∧
      (forall {M N : BHist}, MatrixSingletonClassifier M N ->
        CommRingSingletonClassifier (DeterminantSingletonDet M) (DeterminantSingletonDet N)) ∧
      (forall {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        CommRingSingletonClassifier (DeterminantSingletonDet (MatrixSingletonMul M N))
          (CommRingSingletonMul (DeterminantSingletonDet M) (DeterminantSingletonDet N))) := by
  have emptyCarrier : DeterminantSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have semantic :
      SemanticNameCert DeterminantSingletonCarrier DeterminantSingletonCarrier
        DeterminantSingletonCarrier DeterminantSingletonClassifier := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact ⟨carrier, carrier, hsame_refl h⟩
      equiv_symm := by
        intro h k same
        exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
      equiv_trans := by
        intro h k l sameHK sameKL
        exact ⟨sameHK.left, sameKL.right.left,
          hsame_trans sameHK.right.right sameKL.right.right⟩
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }
  have endpointIff :
      forall {M r : BHist}, DeterminantSingletonEndpoint M r <->
        MatrixSingletonCarrier M ∧ CommRingSingletonClassifier r CommRingSingletonOne := by
    intro M r
    constructor
    · intro endpoint
      exact endpoint.right
    · intro endpoint
      have matrixEndpoint : MatrixSingletonClassifier M BHist.Empty :=
        ⟨endpoint.left, hsame_refl BHist.Empty, endpoint.left⟩
      have scalarEndpoint : CommRingSingletonClassifier r BHist.Empty :=
        endpoint.right
      exact ⟨⟨matrixEndpoint, scalarEndpoint⟩, endpoint⟩
  have detOne :
      CommRingSingletonClassifier (DeterminantSingletonDet MatrixSingletonOne)
        CommRingSingletonOne := by
    exact ⟨append_eq_empty_iff.mpr
      ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩,
      hsame_refl BHist.Empty,
      append_eq_empty_iff.mpr ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩⟩
  have detClassifier :
      forall {M N : BHist}, MatrixSingletonClassifier M N ->
        CommRingSingletonClassifier (DeterminantSingletonDet M) (DeterminantSingletonDet N) := by
    intro M N classified
    have detM : hsame (DeterminantSingletonDet M) BHist.Empty :=
      append_eq_empty_iff.mpr ⟨classified.left, hsame_refl BHist.Empty⟩
    have detN : hsame (DeterminantSingletonDet N) BHist.Empty :=
      append_eq_empty_iff.mpr ⟨classified.right.left, hsame_refl BHist.Empty⟩
    exact ⟨detM, detN, hsame_trans detM (hsame_symm detN)⟩
  have detMul :
      forall {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        CommRingSingletonClassifier (DeterminantSingletonDet (MatrixSingletonMul M N))
          (CommRingSingletonMul (DeterminantSingletonDet M) (DeterminantSingletonDet N)) := by
    intro M N carrierM carrierN
    have productCarrier : hsame (MatrixSingletonMul M N) BHist.Empty :=
      append_eq_empty_iff.mpr ⟨carrierM, carrierN⟩
    have detProduct : hsame (DeterminantSingletonDet (MatrixSingletonMul M N)) BHist.Empty :=
      append_eq_empty_iff.mpr ⟨productCarrier, hsame_refl BHist.Empty⟩
    exact ⟨detProduct, hsame_refl BHist.Empty, detProduct⟩
  exact ⟨semantic, endpointIff, detOne, detClassifier, detMul⟩

theorem DeterminantSingleton_endpoint_correspondence {M N r : BHist} :
    let det : BHist -> BHist := fun _ => BHist.Empty
    let Delta : BHist -> BHist -> Prop := fun M r =>
      MatrixSingletonClassifier M MatrixSingletonOne ∧
        CommRingSingletonClassifier r CommRingSingletonOne
    (Delta M r <->
        MatrixSingletonCarrier M ∧ CommRingSingletonClassifier r CommRingSingletonOne) ∧
      CommRingSingletonClassifier (det MatrixSingletonOne) CommRingSingletonOne ∧
      (MatrixSingletonClassifier M N -> CommRingSingletonClassifier (det M) (det N)) ∧
      CommRingSingletonClassifier (det (MatrixSingletonMul M N))
        (CommRingSingletonMul (det M) (det N)) := by
  dsimp
  constructor
  · constructor
    · intro delta
      exact And.intro delta.left.left delta.right
    · intro endpoint
      have oneCarrier : MatrixSingletonCarrier MatrixSingletonOne := hsame_refl BHist.Empty
      exact And.intro
        (And.intro endpoint.left (And.intro oneCarrier endpoint.left)) endpoint.right
  · constructor
    · exact And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    · constructor
      · intro _classified
        exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
      · exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem DeterminantSingletonEndpoint_correspondence {M r : BHist} :
    (DeterminantSingletonEndpoint M r ↔
      BEDC.Derived.MatrixUp.MatrixSingletonCarrier M ∧
        BEDC.Derived.CommRingUp.CommRingSingletonClassifier r BHist.Empty) ∧
      BEDC.Derived.CommRingUp.CommRingSingletonClassifier
        (DeterminantSingletonDet BEDC.Derived.MatrixUp.MatrixSingletonOne) BHist.Empty ∧
      (∀ {N : BHist}, BEDC.Derived.MatrixUp.MatrixSingletonClassifier M N →
        BEDC.Derived.CommRingUp.CommRingSingletonClassifier
          (DeterminantSingletonDet M) (DeterminantSingletonDet N)) ∧
      (∀ {N : BHist}, BEDC.Derived.MatrixUp.MatrixSingletonCarrier M →
        BEDC.Derived.MatrixUp.MatrixSingletonCarrier N →
          BEDC.Derived.CommRingUp.CommRingSingletonClassifier
            (DeterminantSingletonDet (BEDC.Derived.MatrixUp.MatrixSingletonMul M N))
            (BEDC.Derived.CommRingUp.CommRingSingletonMul
              (DeterminantSingletonDet M) (DeterminantSingletonDet N))) := by
  constructor
  · constructor
    · intro endpoint
      exact And.intro endpoint.right.left endpoint.right.right
    · intro data
      have matrixEndpoint : MatrixSingletonClassifier M BHist.Empty :=
        ⟨data.left, hsame_refl BHist.Empty, data.left⟩
      have scalarEndpoint : CommRingSingletonClassifier r BHist.Empty :=
        data.right
      exact ⟨⟨matrixEndpoint, scalarEndpoint⟩, data⟩
  · constructor
    · exact ⟨append_eq_empty_iff.mpr
        ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩,
        hsame_refl BHist.Empty,
        append_eq_empty_iff.mpr ⟨hsame_refl BHist.Empty, hsame_refl BHist.Empty⟩⟩
    · constructor
      · intro N classified
        have detM : hsame (DeterminantSingletonDet M) BHist.Empty :=
          append_eq_empty_iff.mpr ⟨classified.left, hsame_refl BHist.Empty⟩
        have detN : hsame (DeterminantSingletonDet N) BHist.Empty :=
          append_eq_empty_iff.mpr ⟨classified.right.left, hsame_refl BHist.Empty⟩
        exact ⟨detM, detN, hsame_trans detM (hsame_symm detN)⟩
      · intro N carrierM carrierN
        have productCarrier : hsame (MatrixSingletonMul M N) BHist.Empty :=
          append_eq_empty_iff.mpr ⟨carrierM, carrierN⟩
        have detProduct : hsame (DeterminantSingletonDet (MatrixSingletonMul M N))
            BHist.Empty :=
          append_eq_empty_iff.mpr ⟨productCarrier, hsame_refl BHist.Empty⟩
        exact ⟨detProduct, hsame_refl BHist.Empty, detProduct⟩

end BEDC.Derived.DeterminantUp
