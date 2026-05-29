import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_consumer_nonescape_obligations [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported replay netRead ->
        Cont netRead sealRow compactRead ->
          PkgSig bundle compactRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                    hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row readback ∨ hsame row sealRow ∨
                        Cont exported replay netRead ∨ Cont netRead sealRow compactRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                    hsame row compactRead)
                hsame ∧
              UnaryHistory netRead ∧ UnaryHistory compactRead ∧
                Cont exported replay netRead ∧ Cont netRead sealRow compactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet netRoute compactRoute compactPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, sealRowUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed exportedUnary replayUnary netRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed netUnary sealRowUnary compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨
              hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row readback ∨ hsame row sealRow ∨
                  Cont exported replay netRead ∨ Cont netRead sealRow compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead
        ⟨hsame_refl compactRead, compactUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr compactRoute))))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, compactPkg, source.left⟩
  }
  exact ⟨cert, netUnary, compactUnary, netRoute, compactRoute⟩

end BEDC.Derived.ClosedboundedintervalUp
