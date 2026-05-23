import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessCarrierAdmissionTightening [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name publicRead ->
            SemanticNameCert
                (fun row : BHist => hsame row name ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row name ∧ Cont basic eta analytic ∧
                    Cont analytic functional transports ∧ Cont pole zeroLedger gamma ∧
                      Cont transports routes provenance ∧ Cont routes name publicRead)
                (fun row : BHist =>
                  hsame row name ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory publicRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet routesUnary nameUnary publicRoute
  obtain ⟨basicRoute, analyticRoute, poleRoute, provenanceRoute, namePkg,
    provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary publicRoute
  have sourceName : (fun row : BHist => hsame row name ∧ UnaryHistory row) name := by
    exact ⟨hsame_refl name, nameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∧ Cont basic eta analytic ∧
              Cont analytic functional transports ∧ Cont pole zeroLedger gamma ∧
                Cont transports routes provenance ∧ Cont routes name publicRead)
          (fun row : BHist =>
            hsame row name ∧ PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro name sourceName
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, basicRoute, analyticRoute, poleRoute, provenanceRoute,
            publicRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, namePkg, provenancePkg⟩
    }
  exact ⟨cert, publicUnary, namePkg, provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
