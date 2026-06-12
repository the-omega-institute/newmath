import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPublicConsumerSurface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead coverRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported dyadic netRead ->
        Cont exported stream coverRead ->
          Cont netRead coverRead compactRead ->
            PkgSig bundle compactRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row lower ∨ hsame row upper ∨ hsame row dyadic ∨
                      hsame row stream ∨ Cont exported dyadic netRead ∨
                        Cont exported stream coverRead ∨ Cont netRead coverRead compactRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                      hsame row compactRead)
                  hsame ∧
                UnaryHistory netRead ∧ UnaryHistory coverRead ∧ UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet exportedDyadicNet exportedStreamCover netCoverCompact compactPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed exportedUnary dyadicUnary exportedDyadicNet
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed exportedUnary streamUnary exportedStreamCover
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed netReadUnary coverReadUnary netCoverCompact
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row dyadic ∨ hsame row stream ∨
              Cont exported dyadic netRead ∨ Cont exported stream coverRead ∨
                Cont netRead coverRead compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compactRead ⟨hsame_refl compactRead, compactReadUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr netCoverCompact)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, compactPkg, source.left⟩
  }
  exact ⟨cert, netReadUnary, coverReadUnary, compactReadUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
