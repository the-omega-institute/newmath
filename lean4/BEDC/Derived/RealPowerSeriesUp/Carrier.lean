import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {coeff center argument radius windows partialSums majorant endpoint transport replay
      provenance localName evalRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier coeff center argument radius windows partialSums majorant endpoint
        transport replay provenance localName bundle pkg ->
      Cont coeff windows evalRead ->
        Cont evalRead endpoint namedRead ->
          PkgSig bundle localName pkg ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row coeff ∨ hsame row center ∨ hsame row argument ∨
                      hsame row radius ∨ hsame row windows ∨ hsame row partialSums ∨
                        hsame row majorant ∨ hsame row endpoint ∨ hsame row evalRead ∨
                          hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory evalRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RealPowerSeriesCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier evalRoute namedRoute localNamePkg namedReadPkg
  obtain ⟨coeffUnary, _centerUnary, _argumentUnary, _radiusUnary, windowsUnary,
    _partialSumsUnary, _majorantUnary, endpointUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _coeffWindow, _radiusMajorant, _majorantEndpoint,
    provenancePkg⟩ := carrier
  have evalUnary : UnaryHistory evalRead :=
    unary_cont_closed coeffUnary windowsUnary evalRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed evalUnary endpointUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coeff ∨ hsame row center ∨ hsame row argument ∨
              hsame row radius ∨ hsame row windows ∨ hsame row partialSums ∨
                hsame row majorant ∨ hsame row endpoint ∨ hsame row evalRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, namedReadPkg⟩
  }
  exact ⟨cert, evalUnary, namedUnary⟩

end BEDC.Derived.RealPowerSeriesUp
