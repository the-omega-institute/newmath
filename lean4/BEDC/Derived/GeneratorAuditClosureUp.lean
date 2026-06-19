import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GeneratorAuditClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GeneratorAuditClosureCarrier [AskSetup] [PackageSetup]
    (generator classifier accepted audit transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  UnaryHistory generator ∧ UnaryHistory classifier ∧ UnaryHistory accepted ∧
    UnaryHistory audit ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ hsame transport transport ∧
        hsame accepted BHist.Empty ∧ hsame replay BHist.Empty ∧
          Cont generator classifier accepted ∧ Cont accepted audit replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem GeneratorAuditClosureCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {generator classifier accepted audit transport replay provenance localName acceptedRead auditRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorAuditClosureCarrier generator classifier accepted audit transport replay provenance localName
        bundle pkg ->
      Cont generator classifier acceptedRead ->
        Cont accepted audit auditRead ->
          Cont auditRead replay consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row consumerRead)
                  (fun row : BHist =>
                    hsame row generator ∨ hsame row classifier ∨ hsame row accepted ∨
                      hsame row audit)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle consumerRead pkg)
                  hsame ∧ Cont generator classifier acceptedRead ∧
                Cont accepted audit auditRead ∧ Cont auditRead replay consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier generatorRead auditReadRoute consumerReadRoute consumerPkg
  obtain
    ⟨_generatorUnary, _classifierUnary, _acceptedUnary, _auditUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _transportSelf, acceptedEmpty,
      replayEmpty, generatorAccepted, _acceptedReplay, provenancePkg, localNamePkg⟩ := carrier
  have acceptedReadAccepted : hsame acceptedRead accepted :=
    hsame_trans generatorRead generatorAccepted.symm
  have auditReadAudit : hsame auditRead audit := by
    cases acceptedEmpty
    exact auditReadRoute.trans (append_empty_left audit)
  have consumerReadAudit : hsame consumerRead audit := by
    have consumerReadAuditRead : hsame consumerRead auditRead := by
      cases replayEmpty
      exact consumerReadRoute.trans (append_empty_right auditRead)
    exact hsame_trans consumerReadAuditRead auditReadAudit
  have sourceAcceptedRead :
      (fun row : BHist =>
        hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row consumerRead)
        acceptedRead := by
    exact Or.inl (hsame_refl acceptedRead)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row generator ∨ hsame row classifier ∨ hsame row accepted ∨ hsame row audit)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle consumerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro acceptedRead sourceAcceptedRead
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        cases sourceRow with
        | inl rowAcceptedRead =>
            exact Or.inr (Or.inr (Or.inl (hsame_trans rowAcceptedRead acceptedReadAccepted)))
        | inr rest =>
            cases rest with
            | inl rowAuditRead =>
                exact Or.inr (Or.inr (Or.inr (hsame_trans rowAuditRead auditReadAudit)))
            | inr rowConsumerRead =>
                exact Or.inr (Or.inr (Or.inr (hsame_trans rowConsumerRead consumerReadAudit)))
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨provenancePkg, localNamePkg, consumerPkg⟩
    }
  exact ⟨cert, generatorRead, auditReadRoute, consumerReadRoute⟩

theorem GeneratorAuditClosureCarrier_metacic_sibling_route [AskSetup] [PackageSetup]
    {generator classifier accepted audit transport replay provenance localName acceptedRead auditRead
      siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorAuditClosureCarrier generator classifier accepted audit transport replay provenance
        localName bundle pkg →
      Cont generator classifier acceptedRead →
        Cont accepted audit auditRead →
          Cont auditRead provenance siblingRead →
            PkgSig bundle siblingRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row siblingRead ∨
                      hsame row accepted ∨ hsame row audit ∨ hsame row provenance)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont generator classifier acceptedRead ∧
                      Cont accepted audit auditRead ∧ Cont auditRead provenance siblingRead ∧
                        PkgSig bundle siblingRead pkg)
                  hsame ∧
                UnaryHistory siblingRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier generatorRead auditReadRoute siblingReadRoute siblingPkg
  obtain
    ⟨generatorUnary, classifierUnary, acceptedUnary, auditUnary, _transportUnary, _replayUnary,
      provenanceUnary, _localNameUnary, _transportSelf, acceptedEmpty, _replayEmpty,
      generatorAccepted, _acceptedReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have acceptedReadAccepted : hsame acceptedRead accepted :=
    hsame_trans generatorRead generatorAccepted.symm
  have auditReadAudit : hsame auditRead audit := by
    cases acceptedEmpty
    exact auditReadRoute.trans (append_empty_left audit)
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed generatorUnary classifierUnary generatorRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed acceptedUnary auditUnary auditReadRoute
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed auditReadUnary provenanceUnary siblingReadRoute
  have sourceSibling :
      (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row) siblingRead := by
    exact ⟨hsame_refl siblingRead, siblingUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row siblingRead ∨
              hsame row accepted ∨ hsame row audit ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont generator classifier acceptedRead ∧
              Cont accepted audit auditRead ∧ Cont auditRead provenance siblingRead ∧
                PkgSig bundle siblingRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro siblingRead sourceSibling
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, generatorRead, auditReadRoute, siblingReadRoute, siblingPkg⟩
  }
  exact ⟨cert, siblingUnary⟩

theorem GeneratorAuditClosureCarrier_consumer_nonescape [AskSetup] [PackageSetup]
    {generator classifier accepted audit transport replay provenance localName acceptedRead auditRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorAuditClosureCarrier generator classifier accepted audit transport replay provenance localName
        bundle pkg ->
      Cont generator classifier acceptedRead ->
        Cont accepted audit auditRead ->
          Cont auditRead replay consumerRead ->
            PkgSig bundle consumerRead pkg ->
              hsame consumerRead audit ∧
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      hsame row generator ∨ hsame row classifier ∨ hsame row accepted ∨
                        hsame row audit)
                    (fun _row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle consumerRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier generatorRead auditReadRoute consumerReadRoute consumerPkg
  obtain
    ⟨_generatorUnary, _classifierUnary, _acceptedUnary, _auditUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localNameUnary, _transportSelf, acceptedEmpty,
      replayEmpty, generatorAccepted, _acceptedReplay, provenancePkg, localNamePkg⟩ := carrier
  have acceptedReadAccepted : hsame acceptedRead accepted :=
    hsame_trans generatorRead generatorAccepted.symm
  have auditReadAudit : hsame auditRead audit := by
    cases acceptedEmpty
    exact auditReadRoute.trans (append_empty_left audit)
  have consumerReadAudit : hsame consumerRead audit := by
    have consumerReadAuditRead : hsame consumerRead auditRead := by
      cases replayEmpty
      exact consumerReadRoute.trans (append_empty_right auditRead)
    exact hsame_trans consumerReadAuditRead auditReadAudit
  have sourceAcceptedRead :
      (fun row : BHist =>
        hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row consumerRead)
        acceptedRead := by
    exact Or.inl (hsame_refl acceptedRead)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row acceptedRead ∨ hsame row auditRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row generator ∨ hsame row classifier ∨ hsame row accepted ∨ hsame row audit)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro acceptedRead sourceAcceptedRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow with
      | inl rowAcceptedRead =>
          exact Or.inr (Or.inr (Or.inl (hsame_trans rowAcceptedRead acceptedReadAccepted)))
      | inr rest =>
          cases rest with
          | inl rowAuditRead =>
              exact Or.inr (Or.inr (Or.inr (hsame_trans rowAuditRead auditReadAudit)))
          | inr rowConsumerRead =>
              exact Or.inr (Or.inr (Or.inr (hsame_trans rowConsumerRead consumerReadAudit)))
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨provenancePkg, localNamePkg, consumerPkg⟩
  }
  exact ⟨consumerReadAudit, cert⟩

end BEDC.Derived.GeneratorAuditClosureUp
