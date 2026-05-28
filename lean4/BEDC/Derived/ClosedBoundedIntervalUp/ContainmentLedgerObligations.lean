import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_containment_ledger_obligations [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported containmentRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont order rational containmentRead ->
        Cont containmentRead dyadic ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                    hsame row rational ∨ hsame row dyadic ∨ Cont order rational containmentRead ∨
                      Cont containmentRead dyadic ledgerRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle ledgerRead pkg ∧ hsame row ledgerRead)
                hsame ∧ hsame order (append lower upper) ∧ UnaryHistory containmentRead ∧
              UnaryHistory ledgerRead ∧ Cont order rational containmentRead ∧
                Cont containmentRead dyadic ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet containmentRoute ledgerRoute ledgerPkg
  obtain ⟨_lowerUnary, _upperUnary, orderUnary, rationalUnary, dyadicUnary, _streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, endpointRoute, _containmentCarrierRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have containmentUnary : UnaryHistory containmentRead :=
    unary_cont_closed orderUnary rationalUnary containmentRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed containmentUnary dyadicUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨
              hsame row rational ∨ hsame row dyadic ∨ Cont order rational containmentRead ∨
                Cont containmentRead dyadic ledgerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle ledgerRead pkg ∧ hsame row ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ledgerRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, ledgerPkg, source.left⟩
  }
  exact
    ⟨cert, endpointRoute, containmentUnary, ledgerUnary, containmentRoute, ledgerRoute⟩

end BEDC.Derived.ClosedboundedintervalUp
