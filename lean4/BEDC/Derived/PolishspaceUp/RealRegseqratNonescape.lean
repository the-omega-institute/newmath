import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRealRegseqratNonescape [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName denseRead regularRead realRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger
        alignment transport route provenance localName bundle pkg ->
      Cont separable stream denseRead ->
        Cont denseRead readback regularRead ->
          Cont regularRead ledger realRead ->
            Cont realRead alignment finalRead ->
              PkgSig bundle finalRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                        hsame row alignment ∨ hsame row finalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle finalRead pkg ∧
                        Cont realRead alignment finalRead)
                    hsame ∧
                  UnaryHistory denseRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory realRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier separableStreamDense denseReadbackRegular regularLedgerReal
    realAlignmentFinal finalPkg
  obtain ⟨_metricUnary, _completeUnary, separableUnary, streamUnary, readbackUnary,
    ledgerUnary, alignmentUnary, _transportUnary, _localNameUnary,
    _metricCompleteAlignment, _alignmentStreamReadback, _ledgerTransportRoute,
    _provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed denseUnary readbackUnary denseReadbackRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary ledgerUnary regularLedgerReal
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed realUnary alignmentUnary realAlignmentFinal
  have sourceFinal :
      (fun row : BHist => hsame row finalRead ∧ UnaryHistory row) finalRead := by
    exact ⟨hsame_refl finalRead, finalUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro finalRead sourceFinal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, finalPkg, realAlignmentFinal⟩
    }
  · exact ⟨denseUnary, regularUnary, realUnary, finalUnary⟩

end BEDC.Derived.PolishspaceUp
