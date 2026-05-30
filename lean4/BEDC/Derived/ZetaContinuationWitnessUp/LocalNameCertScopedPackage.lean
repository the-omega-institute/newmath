import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessLocalNameCertScopedPackage [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name packageRead →
            PkgSig bundle packageRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger
                      gamma transports routes provenance name bundle pkg ∧
                        (hsame row name ∨ hsame row packageRead))
                  (fun row : BHist => UnaryHistory row ∧ (hsame row name ∨ hsame row packageRead))
                  (fun row : BHist =>
                    PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle packageRead pkg ∧
                        (hsame row name ∨ hsame row packageRead))
                  hsame ∧
                UnaryHistory packageRead ∧ hsame packageRead (append routes name) ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert ProbeBundle UnaryHistory hsame
  intro packet routesUnary nameUnary routesNamePackage packageReadPkg
  have packetKeep := packet
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed routesUnary nameUnary routesNamePackage
  have sourceName :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
          transports routes provenance name bundle pkg ∧
            (hsame row name ∨ hsame row packageRead)) name := by
    exact ⟨packetKeep, Or.inl (hsame_refl name)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧
                (hsame row name ∨ hsame row packageRead))
          (fun row : BHist => UnaryHistory row ∧ (hsame row name ∨ hsame row packageRead))
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle packageRead pkg ∧ (hsame row name ∨ hsame row packageRead))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro name sourceName
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
          intro row other sameRows source
          cases source.right with
          | inl sameName =>
              exact ⟨source.left, Or.inl (hsame_trans (hsame_symm sameRows) sameName)⟩
          | inr samePackage =>
              exact ⟨source.left, Or.inr (hsame_trans (hsame_symm sameRows) samePackage)⟩
      }
      pattern_sound := by
        intro row source
        cases source.right with
        | inl sameName =>
            exact ⟨unary_transport nameUnary (hsame_symm sameName), Or.inl sameName⟩
        | inr samePackage =>
            exact ⟨unary_transport packageReadUnary (hsame_symm samePackage), Or.inr samePackage⟩
      ledger_sound := by
        intro _row source
        exact ⟨namePkg, provenancePkg, packageReadPkg, source.right⟩
    }
  exact
    ⟨cert, packageReadUnary, routesNamePackage, namePkg, provenancePkg, packageReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
