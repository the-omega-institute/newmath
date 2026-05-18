import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_prefix_transport_exhaustion [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name prefixRead endpoint transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont schedule start prefixRead ->
        Cont source prefixRead endpoint ->
          hsame endpoint transported ->
            PkgSig bundle endpoint pkg ->
              PkgSig bundle transported pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    HistTimeStreamCarrier source schedule start replay transport provenance name
                      bundle pkg ∧ hsame row transported)
                  (fun row : BHist => Cont schedule start prefixRead ∧ hsame row transported)
                  (fun _row : BHist =>
                    Cont source prefixRead endpoint ∧ hsame endpoint transported ∧
                      PkgSig bundle transported pkg)
                  hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory transported := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier schedulePrefix sourcePrefixEndpoint endpointTransported _endpointPkg
    transportedPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, startUnary, _replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed scheduleUnary startUnary schedulePrefix
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary prefixUnary sourcePrefixEndpoint
  have transportedUnary : UnaryHistory transported :=
    unary_transport endpointUnary endpointTransported
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row transported)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro transported
        (And.intro carrierWitness (hsame_refl transported))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row transported)
        (fun row : BHist => Cont schedule start prefixRead ∧ hsame row transported)
        (fun _row : BHist =>
          Cont source prefixRead endpoint ∧ hsame endpoint transported ∧
            PkgSig bundle transported pkg)
        hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact And.intro schedulePrefix sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨sourcePrefixEndpoint, endpointTransported, transportedPkg⟩
    }
  exact And.intro semantic (And.intro prefixUnary transportedUnary)

end BEDC.Derived.HistTimeStreamUp
