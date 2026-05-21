import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_package_provenance_exactness [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
      UnaryHistory name →
      Cont routes name publicRead →
      PkgSig bundle publicRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                hsame row transports ∨ hsame row routes ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row publicRead)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame ∧
        UnaryHistory publicRead ∧ hsame publicRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet routesUnary nameUnary routeRead publicReadPkg
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary routeRead
  have publicSource :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                hsame row transports ∨ hsame row routes ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row publicRead)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead publicSource
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr source.left))))))))))
      ledger_sound := by
        intro row source
        exact ⟨namePkg, provenancePkg, publicReadPkg, source.left⟩
    }
  exact ⟨cert, publicUnary, routeRead⟩

end BEDC.Derived.ZetaContinuationWitnessUp
