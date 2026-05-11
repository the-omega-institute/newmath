import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteVectorPacket [AskSetup] [PackageSetup]
    (length spine pairs component ledger provenance hidden endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory pairs ∧
    UnaryHistory component ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      UnaryHistory hidden ∧ UnaryHistory endpoint ∧ Cont length spine endpoint ∧
        PkgSig bundle endpoint pkg

theorem FiniteVectorPacket_length_index_transport [AskSetup] [PackageSetup]
    {length spine pairs component ledger provenance hidden endpoint length' spine' pairs'
      component' ledger' provenance' hidden' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame pairs pairs' ->
            hsame component component' ->
              hsame ledger ledger' ->
                hsame provenance provenance' ->
                  hsame hidden hidden' ->
                    Cont length' spine' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        FiniteVectorPacket length' spine' pairs' component' ledger'
                            provenance' hidden' endpoint' bundle pkg ∧
                          hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro packet sameLength sameSpine samePairs sameComponent sameLedger sameProvenance
    sameHidden endpointCont' endpointPkg'
  obtain ⟨lengthUnary, spineUnary, pairsUnary, componentUnary, ledgerUnary,
    provenanceUnary, hiddenUnary, _endpointUnary, endpointCont, _endpointPkg⟩ := packet
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have pairsUnary' : UnaryHistory pairs' :=
    unary_transport pairsUnary samePairs
  have componentUnary' : UnaryHistory component' :=
    unary_transport componentUnary sameComponent
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have hiddenUnary' : UnaryHistory hidden' :=
    unary_transport hiddenUnary sameHidden
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed lengthUnary' spineUnary' endpointCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLength sameSpine endpointCont endpointCont'
  exact And.intro
    (And.intro lengthUnary'
      (And.intro spineUnary'
        (And.intro pairsUnary'
          (And.intro componentUnary'
            (And.intro ledgerUnary'
              (And.intro provenanceUnary'
                (And.intro hiddenUnary'
                  (And.intro endpointUnary'
                    (And.intro endpointCont' endpointPkg')))))))))
    sameEndpoint

theorem FiniteVectorPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {length spine pairs component ledger provenance hidden endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint
            bundle pkg ∧ hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig NameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem FiniteVectorPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {length spine pairs component ledger provenance hidden endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row endpoint ∨ hsame row ledger ∨ hsame row provenance)
        (fun row : BHist => hsame row endpoint ∨ hsame row ledger ∨ hsame row provenance)
        (fun row : BHist => hsame row endpoint ∨ hsame row ledger ∨ hsame row provenance)
        hsame := by
  -- BEDC touchpoint anchor: BHist FiniteVectorPacket hsame
  intro packet
  obtain ⟨_lengthUnary, _spineUnary, _pairsUnary, _componentUnary, _ledgerUnary,
    _provenanceUnary, _hiddenUnary, _endpointUnary, _endpointCont, _endpointPkg⟩ := packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (Or.inl (hsame_refl endpoint))
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | inl endpointRow =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) endpointRow)
        | inr rest =>
            cases rest with
            | inl ledgerRow =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) ledgerRow))
            | inr provenanceRow =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) provenanceRow))
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }

def FiniteVectorSame
    (n spine pairs routes provenance ledger n' spine' pairs' routes' provenance'
      ledger' : BHist) : Prop :=
  hsame n n' ∧
    hsame spine spine' ∧
      hsame pairs pairs' ∧
        hsame routes routes' ∧
          hsame provenance provenance' ∧
            Cont routes provenance ledger ∧
              Cont routes' provenance' ledger'

theorem FiniteVectorSame_componentwise_ledger_exactness
    {n spine pairs routes provenance ledger n' spine' pairs' routes' provenance'
      ledger' : BHist} :
    FiniteVectorSame n spine pairs routes provenance ledger n' spine' pairs' routes'
        provenance' ledger' →
      hsame n n' ∧
        hsame spine spine' ∧
          hsame pairs pairs' ∧
            hsame ledger ledger' ∧
              Cont routes provenance ledger ∧ Cont routes' provenance' ledger' := by
  intro same
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame same.right.right.right.left same.right.right.right.right.left
      same.right.right.right.right.right.left same.right.right.right.right.right.right
  exact And.intro same.left
    (And.intro same.right.left
      (And.intro same.right.right.left
        (And.intro sameLedger
          (And.intro same.right.right.right.right.right.left
            same.right.right.right.right.right.right))))

def FiniteVectorComponentLedger [AskSetup] [PackageSetup]
    (n spine pairs component ledger routes provenance hidden : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory n ∧ UnaryHistory spine ∧ UnaryHistory pairs ∧ UnaryHistory component ∧
    UnaryHistory ledger ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
      UnaryHistory hidden ∧ Cont n spine pairs ∧ Cont pairs component ledger ∧
        Cont ledger routes provenance ∧ PkgSig bundle provenance pkg

theorem FiniteVectorComponentLedger_transport [AskSetup] [PackageSetup]
    {n spine pairs component ledger routes provenance hidden n' spine' pairs' component'
      ledger' routes' provenance' hidden' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteVectorComponentLedger n spine pairs component ledger routes provenance hidden
        bundle pkg ->
      hsame n n' -> hsame spine spine' -> hsame pairs pairs' ->
        hsame component component' -> hsame routes routes' -> hsame hidden hidden' ->
          Cont n' spine' pairs' -> Cont pairs' component' ledger' ->
            Cont ledger' routes' provenance' -> PkgSig bundle provenance' pkg ->
              FiniteVectorComponentLedger n' spine' pairs' component' ledger' routes'
                  provenance' hidden' bundle pkg ∧
                hsame ledger ledger' ∧ hsame provenance provenance' := by
  intro source sameN sameSpine samePairs sameComponent sameRoutes sameHidden targetPairs
    targetLedger targetProvenance targetPkg
  obtain ⟨nUnary, spineUnary, pairsUnary, componentUnary, _ledgerUnary, routesUnary,
    _provenanceUnary, hiddenUnary, _sourcePairs, sourceLedger, sourceProvenance,
    _sourcePkg⟩ := source
  have nUnary' : UnaryHistory n' := unary_transport nUnary sameN
  have spineUnary' : UnaryHistory spine' := unary_transport spineUnary sameSpine
  have pairsUnary' : UnaryHistory pairs' := unary_transport pairsUnary samePairs
  have componentUnary' : UnaryHistory component' :=
    unary_transport componentUnary sameComponent
  have routesUnary' : UnaryHistory routes' := unary_transport routesUnary sameRoutes
  have hiddenUnary' : UnaryHistory hidden' := unary_transport hiddenUnary sameHidden
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed pairsUnary' componentUnary' targetLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed ledgerUnary' routesUnary' targetProvenance
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame samePairs sameComponent sourceLedger targetLedger
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameRoutes sourceProvenance targetProvenance
  exact
    ⟨⟨nUnary', spineUnary', pairsUnary', componentUnary', ledgerUnary', routesUnary',
      provenanceUnary', hiddenUnary', targetPairs, targetLedger, targetProvenance,
      targetPkg⟩, sameLedger, sameProvenance⟩

end BEDC.Derived.FiniteVectorUp
