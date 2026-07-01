import BEDC.Derived.PhysicalLawBridgeUp.ObligationPackage

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PhysicalLawBridgeCarrier_scoped_tastegate_route [AskSetup] [PackageSetup]
    {law empirical bridge object fit failure transport replay provenance name scopedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay
        provenance name →
      Cont law empirical bridge →
        Cont bridge object fit →
          Cont fit failure scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                      hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                        hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                          hsame row name ∨ hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont law empirical bridge ∧
                      Cont bridge object fit ∧ Cont fit failure scopedRead ∧
                        PkgSig bundle scopedRead pkg)
                  hsame ∧
                UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier lawEmpiricalBridge bridgeObjectFit fitFailureScoped scopedPkg
  obtain ⟨_lawUnary, _empiricalUnary, _bridgeUnary, _objectUnary, fitUnary,
    failureUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _carrierLawEmpiricalBridge, _objectFitFailure, _transportReplayProvenance⟩ :=
    carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed fitUnary failureUnary fitFailureScoped
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont law empirical bridge ∧ Cont bridge object fit ∧
              Cont fit failure scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lawEmpiricalBridge, bridgeObjectFit, fitFailureScoped, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.PhysicalLawBridgeUp
