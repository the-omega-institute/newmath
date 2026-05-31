import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSeparabilityCarrier [AskSetup] [PackageSetup] (ratEnumeration dyadicTolerance
    streamWindow regseqReadback sealRow densityLedger transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory ratEnumeration ∧ UnaryHistory dyadicTolerance ∧ UnaryHistory streamWindow ∧
    UnaryHistory regseqReadback ∧ UnaryHistory sealRow ∧ UnaryHistory densityLedger ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont ratEnumeration dyadicTolerance streamWindow ∧
          Cont streamWindow regseqReadback sealRow ∧ Cont sealRow densityLedger replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg

theorem RealSeparabilityNameCertObligations [AskSetup] [PackageSetup]
    {ratEnumeration dyadicTolerance streamWindow regseqReadback sealRow densityLedger transport
      replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeparabilityCarrier ratEnumeration dyadicTolerance streamWindow regseqReadback sealRow
        densityLedger transport replay provenance nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RealSeparabilityCarrier ratEnumeration dyadicTolerance streamWindow regseqReadback
              sealRow densityLedger transport replay provenance nameRow bundle pkg ∧
            (hsame row ratEnumeration ∨ hsame row dyadicTolerance ∨ hsame row streamWindow ∨
              hsame row regseqReadback ∨ hsame row sealRow ∨ hsame row densityLedger))
        (fun _row : BHist =>
          Cont ratEnumeration dyadicTolerance streamWindow ∧
            Cont streamWindow regseqReadback sealRow ∧ Cont sealRow densityLedger replay)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierWhole := carrier
  obtain ⟨ratUnary, toleranceUnary, windowUnary, readbackUnary, sealUnary, ledgerUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, ratToleranceWindow,
    windowReadbackSeal, sealLedgerReplay, provenancePkg, _namePkg⟩ := carrier
  have sourceRat :
      (fun row : BHist =>
        RealSeparabilityCarrier ratEnumeration dyadicTolerance streamWindow regseqReadback
            sealRow densityLedger transport replay provenance nameRow bundle pkg ∧
          (hsame row ratEnumeration ∨ hsame row dyadicTolerance ∨ hsame row streamWindow ∨
            hsame row regseqReadback ∨ hsame row sealRow ∨ hsame row densityLedger))
          ratEnumeration := by
    exact ⟨carrierWhole, Or.inl (hsame_refl ratEnumeration)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro ratEnumeration sourceRat
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
        cases source with
        | intro sourceCarrier sourceRows =>
            constructor
            · exact sourceCarrier
            · cases sourceRows with
              | inl sameRat =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameRat)
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTolerance))
                  | inr rest =>
                      cases rest with
                      | inl sameWindow =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)))
                      | inr rest =>
                          cases rest with
                          | inl sameReadback =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameReadback))))
                          | inr rest =>
                              cases rest with
                              | inl sameSeal =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameSeal)))))
                              | inr sameLedger =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (hsame_trans (hsame_symm sameRows) sameLedger)))))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨ratToleranceWindow, windowReadbackSeal, sealLedgerReplay⟩
    ledger_sound := by
      intro _row source
      cases source with
      | intro _sourceCarrier sourceRows =>
          cases sourceRows with
          | inl sameRat =>
              exact ⟨unary_transport ratUnary (hsame_symm sameRat), provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameTolerance =>
                  exact
                    ⟨unary_transport toleranceUnary (hsame_symm sameTolerance), provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameWindow =>
                      exact ⟨unary_transport windowUnary (hsame_symm sameWindow), provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              provenancePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                ⟨unary_transport sealUnary (hsame_symm sameSeal), provenancePkg⟩
                          | inr sameLedger =>
                              exact
                                ⟨unary_transport ledgerUnary (hsame_symm sameLedger),
                                  provenancePkg⟩
  }

end BEDC.Derived.RealUp
