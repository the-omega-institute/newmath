import BEDC.Derived.BaireOneFunctionUp

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireOneFunctionClassifier
    (X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' : BHist) : Prop :=
  hsame X X' ∧ hsame F F' ∧ hsame S S' ∧ hsame Q Q' ∧ hsame R R' ∧
    hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N'

theorem BaireOneFunctionClassifier_component_transport [AskSetup] [PackageSetup]
    {X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      BaireOneFunctionCarrier X' F' S' Q' R' L' H' C' P' N' bundle pkg →
        BaireOneFunctionClassifier X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' →
          UnaryHistory X' ∧ UnaryHistory F' ∧ UnaryHistory S' ∧ UnaryHistory Q' ∧
            UnaryHistory R' ∧ UnaryHistory L' ∧ UnaryHistory H' ∧ UnaryHistory C' ∧
              PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier _targetCarrier classified
  obtain ⟨xUnary, fUnary, sUnary, qUnary, rUnary, lUnary, hUnary, cUnary,
    _pUnary, _nUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    _realHandoffTransport, _transportContinuationProvenance, _provenancePkg,
    _namePkg⟩ := carrier
  obtain ⟨_targetXUnary, _targetFUnary, _targetSUnary, _targetQUnary, _targetRUnary,
    _targetLUnary, _targetHUnary, _targetCUnary, _targetPUnary, _targetNUnary,
    _targetSourceApproxSchedule, _targetScheduleReadbackReal, _targetRealHandoffTransport,
    _targetTransportContinuationProvenance, targetProvenancePkg, targetNamePkg⟩ :=
    _targetCarrier
  obtain ⟨sameX, sameF, sameS, sameQ, sameR, sameL, sameH, sameC, _sameP, _sameN⟩ :=
    classified
  exact
    ⟨unary_transport xUnary sameX, unary_transport fUnary sameF,
      unary_transport sUnary sameS, unary_transport qUnary sameQ,
      unary_transport rUnary sameR, unary_transport lUnary sameL,
      unary_transport hUnary sameH, unary_transport cUnary sameC,
      targetProvenancePkg, targetNamePkg⟩

theorem BaireOneFunctionClassifier_component_namecert_transport
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      BaireOneFunctionCarrier X' F' S' Q' R' L' H' C' P' N' bundle pkg ->
        BaireOneFunctionClassifier X F S Q R L H C P N X' F' S' Q' R' L' H' C' P' N' ->
          Cont S' Q' endpoint ->
            PkgSig bundle endpoint pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row endpoint ∧
                      BaireOneFunctionCarrier X' F' S' Q' R' L' H' C P' N'
                        bundle pkg)
                  (fun row : BHist =>
                    hsame row X' ∨ hsame row F' ∨ hsame row S' ∨ hsame row Q' ∨
                      hsame row R' ∨ hsame row L' ∨ hsame row H' ∨ hsame row C' ∨
                        hsame row P' ∨ hsame row N' ∨ hsame row endpoint)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P' pkg ∧
                      PkgSig bundle endpoint pkg)
                  hsame ∧
                UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier targetCarrier classified endpointRoute endpointPkg
  have targetAtSourceC :
      BaireOneFunctionCarrier X' F' S' Q' R' L' H' C P' N' bundle pkg := by
    obtain ⟨targetXUnary, targetFUnary, targetSUnary, targetQUnary, targetRUnary,
      targetLUnary, targetHUnary, _targetCUnary, targetPUnary, targetNUnary,
      targetSourceApproxSchedule, targetScheduleReadbackReal, targetRealHandoffTransport,
      targetTransportContinuationProvenance, targetProvenancePkg, targetNamePkg⟩ :=
      targetCarrier
    obtain ⟨_sameX, _sameF, _sameS, _sameQ, _sameR, _sameL, _sameH, sameC,
      _sameP, _sameN⟩ := classified
    have transportedContinuation :
        Cont H' C P' := by
      cases sameC
      exact targetTransportContinuationProvenance
    exact
      ⟨targetXUnary, targetFUnary, targetSUnary, targetQUnary, targetRUnary,
        targetLUnary, targetHUnary, unary_transport _targetCUnary (hsame_symm sameC),
        targetPUnary, targetNUnary, targetSourceApproxSchedule,
        targetScheduleReadbackReal, targetRealHandoffTransport,
        transportedContinuation, targetProvenancePkg, targetNamePkg⟩
  obtain ⟨_targetXUnary, _targetFUnary, targetSUnary, targetQUnary, _targetRUnary,
    _targetLUnary, _targetHUnary, _targetCUnary, _targetPUnary, _targetNUnary,
    _targetSourceApproxSchedule, _targetScheduleReadbackReal, _targetRealHandoffTransport,
    _targetTransportContinuationProvenance, targetProvenancePkg, _targetNamePkg⟩ :=
    targetCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed targetSUnary targetQUnary endpointRoute
  have endpointSource :
      (fun row : BHist =>
        hsame row endpoint ∧
          BaireOneFunctionCarrier X' F' S' Q' R' L' H' C P' N' bundle pkg)
          endpoint := by
    exact ⟨hsame_refl endpoint, targetAtSourceC⟩
  have endpointCert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              BaireOneFunctionCarrier X' F' S' Q' R' L' H' C P' N' bundle pkg)
          (fun row : BHist =>
            hsame row X' ∨ hsame row F' ∨ hsame row S' ∨ hsame row Q' ∨
              hsame row R' ∨ hsame row L' ∨ hsame row H' ∨ hsame row C' ∨
                hsame row P' ∨ hsame row N' ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P' pkg ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.left), targetProvenancePkg,
          endpointPkg⟩
  }
  exact ⟨endpointCert, endpointUnary⟩

end BEDC.Derived.BaireOneFunctionUp
