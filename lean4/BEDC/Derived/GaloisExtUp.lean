import BEDC.Derived.SeparableExtUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem GaloisExtSourcePacket_fixed_base_automorphism_source [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint baseFixed actionLedger automorphismLedger :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      UnaryHistory baseFixed ->
        Cont fieldExt baseFixed actionLedger ->
          Cont actionLedger normality automorphismLedger ->
            UnaryHistory actionLedger ∧ UnaryHistory automorphismLedger ∧
              hsame actionLedger (append fieldExt baseFixed) ∧
                hsame automorphismLedger (append actionLedger normality) ∧
                  PkgSig bundle endpoint pkg := by
  intro packet baseFixedUnary actionRow automorphismRow
  have actionUnary : UnaryHistory actionLedger :=
    unary_cont_closed packet.left.left baseFixedUnary actionRow
  have automorphismUnary : UnaryHistory automorphismLedger :=
    unary_cont_closed actionUnary packet.right.left automorphismRow
  exact And.intro actionUnary
    (And.intro automorphismUnary
      (And.intro actionRow
        (And.intro automorphismRow packet.right.right.right.right.right.right)))

theorem GaloisExtSourcePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      SemanticNameCert
        (fun e : BHist => exists p c : BHist, GaloisExtSourcePacket fieldExt polynomial
          generator minimal simpleRoot sepProvenance separable normality separability c p e
          bundle pkg)
        (fun e : BHist => exists p c : BHist, GaloisExtSourcePacket fieldExt polynomial
          generator minimal simpleRoot sepProvenance separable normality separability c p e
          bundle pkg)
        (fun e : BHist => exists p c : BHist, GaloisExtSourcePacket fieldExt polynomial
          generator minimal simpleRoot sepProvenance separable normality separability c p e
          bundle pkg)
        (fun left right : BHist =>
          (exists lp lc : BHist, GaloisExtSourcePacket fieldExt polynomial generator minimal
            simpleRoot sepProvenance separable normality separability lc lp left bundle pkg) /\
            (exists rp rc : BHist, GaloisExtSourcePacket fieldExt polynomial generator minimal
              simpleRoot sepProvenance separable normality separability rc rp right bundle pkg) /\
              hsame left right) := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (Exists.intro provenance (Exists.intro classifier packet))
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

theorem GaloisExtSourcePacket_public_obligation_boundary [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
          separable bundle pkg ∧
        UnaryHistory normality ∧ UnaryHistory separability ∧ UnaryHistory classifier ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont fieldExt separable provenance ∧
            Cont normality separability classifier ∧ Cont provenance classifier endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro packet
  have separableClosure :=
    SeparableExtSourceSurface_dependency_ledger_closure packet.left
  have separableUnary : UnaryHistory separable :=
    separableClosure.right.left
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed packet.right.left packet.right.right.left
      packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left.left separableUnary packet.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary classifierUnary
      packet.right.right.right.right.right.left
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro classifierUnary
          (And.intro provenanceUnary
            (And.intro endpointUnary
               (And.intro packet.right.right.right.left
                 (And.intro packet.right.right.right.right.left
                   (And.intro packet.right.right.right.right.right.left
                     packet.right.right.right.right.right.right))))))))

theorem GaloisExtSourcePacket_automorphism_action_source [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint action actionLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      Cont endpoint normality action ->
        Cont action separability actionLedger ->
          UnaryHistory action ∧ UnaryHistory actionLedger ∧
            hsame action (append endpoint normality) ∧
              hsame actionLedger (append (append endpoint normality) separability) ∧
                PkgSig bundle endpoint pkg := by
  intro packet actionCont actionLedgerCont
  have boundary := GaloisExtSourcePacket_public_obligation_boundary packet
  have actionUnary : UnaryHistory action :=
    unary_cont_closed boundary.right.right.right.right.right.left boundary.right.left actionCont
  have actionLedgerUnary : UnaryHistory actionLedger :=
    unary_cont_closed actionUnary boundary.right.right.left actionLedgerCont
  have actionLedgerReadback : hsame actionLedger (append (append endpoint normality) separability) :=
    hsame_trans actionLedgerCont
      (congrArg (fun h : BHist => append h separability) actionCont)
  exact And.intro actionUnary
    (And.intro actionLedgerUnary
      (And.intro actionCont
        (And.intro actionLedgerReadback
          boundary.right.right.right.right.right.right.right.right.right)))

theorem GaloisExtSourcePacket_galoisgroup_consumer_source_surface [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint action actionLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      Cont endpoint normality action ->
        Cont action separability actionLedger ->
          SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot sepProvenance
              separable bundle pkg ∧
            UnaryHistory normality ∧ UnaryHistory separability ∧ UnaryHistory action ∧
              UnaryHistory actionLedger ∧ hsame action (append endpoint normality) ∧
                hsame actionLedger (append action separability) ∧ PkgSig bundle endpoint pkg := by
  intro packet actionCont actionLedgerCont
  have boundary := GaloisExtSourcePacket_public_obligation_boundary packet
  have actionRows :=
    GaloisExtSourcePacket_automorphism_action_source packet actionCont actionLedgerCont
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro boundary.right.right.left
        (And.intro actionRows.left
          (And.intro actionRows.right.left
            (And.intro actionRows.right.right.left
              (And.intro actionLedgerCont actionRows.right.right.right.right))))))

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

theorem GaloisExtSourceClassifier_symmetric [AskSetup]
    {bundle : ProbeBundle ProbeName}
    {field separable normal automorphism classifier provenance ledger field' separable' normal'
      automorphism' classifier' provenance' ledger' : BHist} :
    (SameSig bundle field field' ∧ SameSig bundle separable separable' ∧
      SameSig bundle normal normal' ∧ SameSig bundle automorphism automorphism' ∧
        SameSig bundle classifier classifier' ∧ hsame provenance provenance' ∧
          hsame ledger ledger') ->
      SameSig bundle field' field ∧ SameSig bundle separable' separable ∧
        SameSig bundle normal' normal ∧ SameSig bundle automorphism' automorphism ∧
          SameSig bundle classifier' classifier ∧ hsame provenance' provenance ∧
            hsame ledger' ledger := by
  intro source
  exact And.intro (sameSig_symm source.left)
    (And.intro (sameSig_symm source.right.left)
      (And.intro (sameSig_symm source.right.right.left)
          (And.intro (sameSig_symm source.right.right.right.left)
            (And.intro (sameSig_symm source.right.right.right.right.left)
              (And.intro (hsame_symm source.right.right.right.right.right.left)
                (hsame_symm source.right.right.right.right.right.right))))))

theorem GaloisExtSourceClassifier_reflexive [AskSetup]
    {bundle : ProbeBundle ProbeName}
    {field separable normal automorphism classifier provenance ledger : BHist}
    (policy : AskPolicy (fun h : BHist => UnaryHistory h)) :
    UnaryHistory field ->
      UnaryHistory separable ->
        UnaryHistory normal ->
          UnaryHistory automorphism ->
            UnaryHistory classifier ->
              SameSig bundle field field ∧ SameSig bundle separable separable ∧
                SameSig bundle normal normal ∧ SameSig bundle automorphism automorphism ∧
                  SameSig bundle classifier classifier ∧ hsame provenance provenance ∧
                    hsame ledger ledger := by
  intro fieldUnary separableUnary normalUnary automorphismUnary classifierUnary
  have fieldSame : SameSig bundle field field :=
    sameSig_refl_under_policy
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      policy fieldUnary
  have separableSame : SameSig bundle separable separable :=
    sameSig_refl_under_policy
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      policy separableUnary
  have normalSame : SameSig bundle normal normal :=
    sameSig_refl_under_policy
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      policy normalUnary
  have automorphismSame : SameSig bundle automorphism automorphism :=
    sameSig_refl_under_policy
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      policy automorphismUnary
  have classifierSame : SameSig bundle classifier classifier :=
    sameSig_refl_under_policy
      (bundle := bundle) (D := fun h : BHist => UnaryHistory h)
      policy classifierUnary
  exact And.intro fieldSame
      (And.intro separableSame
        (And.intro normalSame
          (And.intro automorphismSame
            (And.intro classifierSame
              (And.intro (hsame_refl provenance) (hsame_refl ledger))))))

theorem GaloisExtSourcePacket_normal_separable_stability [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint normality' separability' classifier'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      hsame normality normality' ->
        hsame separability separability' ->
          Cont normality' separability' classifier' ->
            Cont provenance classifier' endpoint' ->
              GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance
                  separable normality' separability' classifier' provenance endpoint' bundle pkg ∧
                hsame classifier classifier' ∧ hsame endpoint endpoint' := by
  intro packet sameNormality sameSeparability classifierRow endpointRow
  have normalityUnary : UnaryHistory normality' :=
    unary_transport packet.right.left sameNormality
  have separabilityUnary : UnaryHistory separability' :=
    unary_transport packet.right.right.left sameSeparability
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameNormality sameSeparability packet.right.right.right.right.left
      classifierRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameClassifier
      packet.right.right.right.right.right.left endpointRow
  have pkgSig : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact packet.right.right.right.right.right.right
  exact And.intro
    (And.intro packet.left
      (And.intro normalityUnary
        (And.intro separabilityUnary
          (And.intro packet.right.right.right.left
            (And.intro classifierRow (And.intro endpointRow pkgSig))))))
    (And.intro sameClassifier sameEndpoint)

theorem GaloisExtSourcePacket_endpoint_empty_inversion [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      hsame endpoint BHist.Empty ->
        hsame fieldExt BHist.Empty /\ hsame separable BHist.Empty /\
          hsame normality BHist.Empty /\ hsame separability BHist.Empty := by
  intro packet endpointEmpty
  have endpointCont : Cont provenance classifier endpoint :=
    packet.right.right.right.right.right.left
  have provenanceClassifierEmpty :
      Cont provenance classifier BHist.Empty :=
    cont_result_hsame_transport endpointCont endpointEmpty
  have provenanceClassifierParts := cont_empty_result_inversion provenanceClassifierEmpty
  have provenanceEmpty : hsame provenance BHist.Empty :=
    provenanceClassifierParts.left
  have classifierEmpty : hsame classifier BHist.Empty :=
    provenanceClassifierParts.right
  have fieldSeparableCont : Cont fieldExt separable provenance :=
    packet.right.right.right.left
  have fieldSeparableEmpty :
      Cont fieldExt separable BHist.Empty :=
    cont_result_hsame_transport fieldSeparableCont provenanceEmpty
  have fieldSeparableParts := cont_empty_result_inversion fieldSeparableEmpty
  have normalitySeparabilityCont : Cont normality separability classifier :=
    packet.right.right.right.right.left
  have normalitySeparabilityEmpty :
      Cont normality separability BHist.Empty :=
    cont_result_hsame_transport normalitySeparabilityCont classifierEmpty
  have normalitySeparabilityParts := cont_empty_result_inversion normalitySeparabilityEmpty
  exact And.intro fieldSeparableParts.left
    (And.intro fieldSeparableParts.right
      (And.intro normalitySeparabilityParts.left normalitySeparabilityParts.right))

theorem GaloisExtSourcePacket_dependency_exactness_ledger [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
        hsame provenance (append fieldExt separable) ∧
          hsame classifier (append normality separability) ∧
            hsame endpoint (append provenance classifier) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have separableSurface :=
    SeparableExtSourceSurface_dependency_ledger_closure packet.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left.left separableSurface.right.left
      packet.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed packet.right.left packet.right.right.left
      packet.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary classifierUnary
      packet.right.right.right.right.right.left
  exact And.intro provenanceUnary
    (And.intro classifierUnary
      (And.intro endpointUnary
        (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                packet.right.right.right.right.right.right)))))

theorem GaloisExtSourcePacket_normal_root_orbit_closure [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint orbitLedger orbitEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      Cont normality provenance orbitLedger ->
        Cont orbitLedger separability orbitEndpoint ->
          UnaryHistory orbitLedger ∧ UnaryHistory orbitEndpoint ∧
            hsame orbitLedger (append normality provenance) ∧
              hsame orbitEndpoint (append (append normality provenance) separability) ∧
                PkgSig bundle endpoint pkg := by
  intro packet orbitLedgerRow orbitEndpointRow
  have boundary :=
    GaloisExtSourcePacket_public_obligation_boundary packet
  have orbitLedgerUnary : UnaryHistory orbitLedger :=
    unary_cont_closed boundary.right.left boundary.right.right.right.right.left orbitLedgerRow
  have orbitEndpointUnary : UnaryHistory orbitEndpoint :=
    unary_cont_closed orbitLedgerUnary boundary.right.right.left orbitEndpointRow
  have orbitEndpointReadback :
      hsame orbitEndpoint (append (append normality provenance) separability) :=
    hsame_trans orbitEndpointRow
      (congrArg (fun h : BHist => append h separability) orbitLedgerRow)
  exact And.intro orbitLedgerUnary
    (And.intro orbitEndpointUnary
      (And.intro orbitLedgerRow
        (And.intro orbitEndpointReadback
          boundary.right.right.right.right.right.right.right.right.right)))

theorem GaloisExtAutomorphismSourceRow_base_fixed_readback [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint automorphism fixedBase action
      automorphismLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance
        separable normality separability classifier provenance endpoint bundle pkg ->
      UnaryHistory automorphism ->
        Cont fieldExt automorphism fixedBase ->
          Cont fixedBase normality action ->
            Cont action provenance automorphismLedger ->
              UnaryHistory fixedBase ∧ UnaryHistory action ∧ UnaryHistory automorphismLedger ∧
                hsame fixedBase (append fieldExt automorphism) ∧
                  hsame action (append fixedBase normality) ∧
                    hsame automorphismLedger (append action provenance) ∧
                      PkgSig bundle endpoint pkg := by
  intro packet automorphismUnary fixedBaseCont actionCont ledgerCont
  have provenanceRows := GaloisExtSourcePacket_dependency_exactness_ledger packet
  have fixedBaseUnary : UnaryHistory fixedBase :=
    unary_cont_closed packet.left.left automorphismUnary fixedBaseCont
  have actionUnary : UnaryHistory action :=
    unary_cont_closed fixedBaseUnary packet.right.left actionCont
  have automorphismLedgerUnary : UnaryHistory automorphismLedger :=
    unary_cont_closed actionUnary provenanceRows.left ledgerCont
  exact And.intro fixedBaseUnary
    (And.intro actionUnary
      (And.intro automorphismLedgerUnary
        (And.intro fixedBaseCont
          (And.intro actionCont
            (And.intro ledgerCont provenanceRows.right.right.right.right.right.right)))))

end BEDC.Derived.GaloisExtUp
