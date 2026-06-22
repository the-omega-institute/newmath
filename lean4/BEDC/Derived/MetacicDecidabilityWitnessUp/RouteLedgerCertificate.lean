import BEDC.Derived.MetacicDecidabilityWitnessUp.DecidabilityWitnessPublicExport

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessCarrier_route_ledger_certificate [AskSetup] [PackageSetup]
    {T S B F R H C P N routeRead provenanceRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg →
      Cont H C routeRead →
        Cont routeRead P provenanceRead →
          Cont provenanceRead N ledgerRead →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row ledgerRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row routeRead ∨ hsame row provenanceRead ∨
                        hsame row ledgerRead)
                  (fun row : BHist =>
                    hsame row ledgerRead ∧ Cont H C routeRead ∧
                      Cont routeRead P provenanceRead ∧
                        Cont provenanceRead N ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                  hsame ∧ UnaryHistory routeRead ∧ UnaryHistory provenanceRead ∧
                UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier routeStep provenanceStep ledgerStep ledgerPkg
  obtain ⟨_tUnary, _sUnary, _bUnary, _fUnary, _rUnary, hUnary, cUnary, pUnary,
    nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed hUnary cUnary routeStep
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed routeUnary pUnary provenanceStep
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nUnary ledgerStep
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary, ledgerPkg⟩
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
          cases sameRows
          exact source
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, routeStep, provenanceStep, ledgerStep, ledgerPkg⟩
    }
  · exact ⟨routeUnary, provenanceUnary, ledgerUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
