import BEDC.Derived.ClosedboundedintervalUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_compact_uniform_source_package [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteNet locatedCover nestedWindow compactUniform : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont exported dyadic finiteNet →
        Cont exported stream locatedCover →
          Cont exported readback nestedWindow →
            Cont exported sealRow compactUniform →
              PkgSig bundle compactUniform pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row compactUniform ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row finiteNet ∨ hsame row locatedCover ∨
                        hsame row nestedWindow ∨ hsame row compactUniform)
                    (fun row : BHist =>
                      hsame row compactUniform ∧ PkgSig bundle compactUniform pkg ∧
                        PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory finiteNet ∧ UnaryHistory locatedCover ∧
                    UnaryHistory nestedWindow ∧ UnaryHistory compactUniform ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet exportedDyadicNet exportedStreamCover exportedReadbackWindow
    exportedSealCompact compactUniformPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute,
    _containmentRoute, _sealRoute, _replayRoute, _nameRoute, provenancePkg,
    _localNamePkg⟩ := packet
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed exportedUnary dyadicUnary exportedDyadicNet
  have locatedCoverUnary : UnaryHistory locatedCover :=
    unary_cont_closed exportedUnary streamUnary exportedStreamCover
  have nestedWindowUnary : UnaryHistory nestedWindow :=
    unary_cont_closed exportedUnary readbackUnary exportedReadbackWindow
  have compactUniformUnary : UnaryHistory compactUniform :=
    unary_cont_closed exportedUnary sealRowUnary exportedSealCompact
  have compactUniformSource :
      (fun row : BHist => hsame row compactUniform ∧ UnaryHistory row) compactUniform := by
    exact ⟨hsame_refl compactUniform, compactUniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactUniform ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row finiteNet ∨ hsame row locatedCover ∨ hsame row nestedWindow ∨
              hsame row compactUniform)
          (fun row : BHist =>
            hsame row compactUniform ∧ PkgSig bundle compactUniform pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactUniform compactUniformSource
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, compactUniformPkg, provenancePkg⟩
  }
  exact
    ⟨cert, finiteNetUnary, locatedCoverUnary, nestedWindowUnary, compactUniformUnary,
      provenancePkg⟩

end BEDC.Derived.ClosedboundedintervalUp
