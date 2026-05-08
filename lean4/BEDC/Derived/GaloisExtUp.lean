import BEDC.Derived.SeparableExtUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp
open BEDC.Derived.SeparableExtUp

theorem GaloisExtClassifier_transport_row
    {field field' separable separable' normal normal' sepFace sepFace' classifier classifier'
      ledger ledger' : BHist} :
    UnaryHistory field' ->
      UnaryHistory separable' ->
        UnaryHistory normal' ->
          UnaryHistory sepFace' ->
            hsame field field' ->
              hsame separable separable' ->
                hsame normal normal' ->
                  hsame sepFace sepFace' ->
                    Cont field separable classifier ->
                      Cont field' separable' classifier' ->
                        Cont normal sepFace ledger ->
                          Cont normal' sepFace' ledger' ->
                            UnaryHistory classifier' ∧
                              UnaryHistory ledger' ∧
                                hsame classifier classifier' ∧ hsame ledger ledger' := by
  intro fieldUnary separableUnary normalUnary sepFaceUnary fieldSame separableSame normalSame
    sepFaceSame classifierCont classifierCont' ledgerCont ledgerCont'
  constructor
  · exact unary_cont_closed fieldUnary separableUnary classifierCont'
  · constructor
    · exact unary_cont_closed normalUnary sepFaceUnary ledgerCont'
    · constructor
      · exact cont_respects_hsame fieldSame separableSame classifierCont classifierCont'
      · exact cont_respects_hsame normalSame sepFaceSame ledgerCont ledgerCont'

def GaloisExtSourcePacket [AskSetup] [PackageSetup]
    (fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
      separable bundle pkg ∧
    UnaryHistory normality ∧ UnaryHistory separability ∧
      Cont fieldExt separable provenance ∧ Cont normality separability classifier ∧
        Cont provenance classifier endpoint ∧ PkgSig bundle endpoint pkg

theorem GaloisExtSourcePacket_normality_obligation_row [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
          separable bundle pkg ∧
        UnaryHistory normality ∧ hsame provenance (append fieldExt separable) ∧
          hsame classifier (append normality separability) ∧
            hsame endpoint (append provenance classifier) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.right.left
        (And.intro packet.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.left
            packet.right.right.right.right.right.right))))

theorem GaloisExtSourcePacket_classifier_transport
    {field field' separable separable' normal normal' simple simple' classifier classifier'
      provenance provenance' ledger ledger' : BHist} :
    UnaryHistory field ->
      UnaryHistory separable ->
        UnaryHistory normal ->
          UnaryHistory simple ->
            hsame field field' ->
              hsame separable separable' ->
                hsame normal normal' ->
                  hsame simple simple' ->
                    Cont field separable classifier ->
                      Cont normal simple provenance ->
                        Cont classifier provenance ledger ->
                          Cont field' separable' classifier' ->
                            Cont normal' simple' provenance' ->
                              Cont classifier' provenance' ledger' ->
                                UnaryHistory classifier' ∧ UnaryHistory provenance' ∧
                                  UnaryHistory ledger' ∧ hsame classifier classifier' ∧
                                    hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro fieldUnary separableUnary normalUnary simpleUnary sameField sameSeparable sameNormal
    sameSimple classifierCont provenanceCont ledgerCont classifierCont' provenanceCont'
    ledgerCont'
  have fieldUnary' : UnaryHistory field' :=
    unary_transport fieldUnary sameField
  have separableUnary' : UnaryHistory separable' :=
    unary_transport separableUnary sameSeparable
  have normalUnary' : UnaryHistory normal' :=
    unary_transport normalUnary sameNormal
  have simpleUnary' : UnaryHistory simple' :=
    unary_transport simpleUnary sameSimple
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed fieldUnary' separableUnary' classifierCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed normalUnary' simpleUnary' provenanceCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed classifierUnary' provenanceUnary' ledgerCont'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameField sameSeparable classifierCont classifierCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameNormal sameSimple provenanceCont provenanceCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameClassifier sameProvenance ledgerCont ledgerCont'
  exact And.intro classifierUnary'
    (And.intro provenanceUnary'
      (And.intro ledgerUnary'
        (And.intro sameClassifier
          (And.intro sameProvenance sameLedger))))

theorem GaloisExtSourceClassifier_transitive [AskSetup]
    {bundle : ProbeBundle ProbeName}
    {field separable normal automorphism classifier provenance ledger field' separable' normal'
      automorphism' classifier' provenance' ledger' field'' separable'' normal'' automorphism''
      classifier'' provenance'' ledger'' : BHist}
    (policy : AskPolicy (fun h : BHist => UnaryHistory h)) :
    UnaryHistory field' ->
      UnaryHistory separable' ->
        UnaryHistory normal' ->
          UnaryHistory automorphism' ->
            UnaryHistory classifier' ->
              (SameSig bundle field field' ∧ SameSig bundle separable separable' ∧
                SameSig bundle normal normal' ∧ SameSig bundle automorphism automorphism' ∧
                  SameSig bundle classifier classifier' ∧ hsame provenance provenance' ∧
                    hsame ledger ledger') ->
                (SameSig bundle field' field'' ∧ SameSig bundle separable' separable'' ∧
                  SameSig bundle normal' normal'' ∧
                    SameSig bundle automorphism' automorphism'' ∧
                      SameSig bundle classifier' classifier'' ∧
                        hsame provenance' provenance'' ∧ hsame ledger' ledger'') ->
                  SameSig bundle field field'' ∧ SameSig bundle separable separable'' ∧
                    SameSig bundle normal normal'' ∧
                      SameSig bundle automorphism automorphism'' ∧
                        SameSig bundle classifier classifier'' ∧
                          hsame provenance provenance'' ∧ hsame ledger ledger'' := by
  intro fieldUnary' separableUnary' normalUnary' automorphismUnary' classifierUnary'
    left right
  have fieldSame : SameSig bundle field field'' :=
    sameSig_trans
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      (h := field) (k := field') (l := field'')
      policy fieldUnary' left.left right.left
  have separableSame : SameSig bundle separable separable'' :=
    sameSig_trans
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      (h := separable) (k := separable') (l := separable'')
      policy separableUnary' left.right.left right.right.left
  have normalSame : SameSig bundle normal normal'' :=
    sameSig_trans
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      (h := normal) (k := normal') (l := normal'')
      policy normalUnary' left.right.right.left right.right.right.left
  have automorphismSame : SameSig bundle automorphism automorphism'' :=
    sameSig_trans
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      (h := automorphism) (k := automorphism') (l := automorphism'')
      policy automorphismUnary' left.right.right.right.left right.right.right.right.left
  have classifierSame : SameSig bundle classifier classifier'' :=
    sameSig_trans
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      (h := classifier) (k := classifier') (l := classifier'')
      policy classifierUnary' left.right.right.right.right.left
        right.right.right.right.right.left
  have provenanceSame : hsame provenance provenance'' :=
    hsame_trans left.right.right.right.right.right.left right.right.right.right.right.right.left
  have ledgerSame : hsame ledger ledger'' :=
    hsame_trans left.right.right.right.right.right.right right.right.right.right.right.right.right
  exact And.intro fieldSame
    (And.intro separableSame
      (And.intro normalSame
        (And.intro automorphismSame
          (And.intro classifierSame
            (And.intro provenanceSame ledgerSame)))))

end BEDC.Derived.GaloisExtUp
