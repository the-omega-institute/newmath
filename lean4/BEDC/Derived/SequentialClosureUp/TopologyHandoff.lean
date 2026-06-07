import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureTopologyHandoff [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N topologyRead closureRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont T U topologyRead ->
        Cont topologyRead L closureRead ->
          Cont closureRead N named ->
            PkgSig bundle named pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row U ∨ hsame row L ∨ hsame row named)
                  (fun row : BHist =>
                    hsame row named ∧ Cont T U topologyRead ∧
                      Cont topologyRead L closureRead ∧ PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory topologyRead ∧ UnaryHistory closureRead ∧
                  UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier topologyRoute closureRoute namedRoute namedPkg
  obtain ⟨topologyUnary, _metricUnary, _sourceUnary, _sequenceUnary, limitUnary,
    requestUnary, _windowUnary, _handoffUnary, _sealUnary, _transportUnary,
    _continuationUnary, _pUnary, nUnary, pPkg, _nPkg⟩ := carrier
  have topologyReadUnary : UnaryHistory topologyRead :=
    unary_cont_closed topologyUnary requestUnary topologyRoute
  have closureReadUnary : UnaryHistory closureRead :=
    unary_cont_closed topologyReadUnary limitUnary closureRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed closureReadUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row T ∨ hsame row U ∨ hsame row L ∨ hsame row named)
          (fun row : BHist =>
            hsame row named ∧ Cont T U topologyRead ∧
              Cont topologyRead L closureRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named
        ⟨hsame_refl named, namedUnary, namedPkg⟩
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, topologyRoute, closureRoute, pPkg⟩
  }
  exact ⟨cert, topologyReadUnary, closureReadUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp
