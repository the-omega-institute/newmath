import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_consumer_obligations [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead uniformRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream netRead ->
        Cont netRead sealRow uniformRead ->
          Cont uniformRead exported consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                      hsame row dyadic ∨ hsame row stream ∨ hsame row sealRow ∨
                        hsame row netRead ∨ hsame row uniformRead ∨
                          hsame row consumerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle consumerRead pkg)
                  hsame ∧
                UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
                  UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory sealRow ∧
                    UnaryHistory netRead ∧ UnaryHistory uniformRead ∧
                      UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet netRoute uniformRoute consumerRoute consumerPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed dyadicUnary streamUnary netRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed netUnary sealRowUnary uniformRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed uniformUnary exportedUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row sealRow ∨ hsame row netRead ∨
                hsame row uniformRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, consumerPkg⟩
  }
  exact
    ⟨cert, lowerUnary, upperUnary, orderUnary, dyadicUnary, streamUnary, sealRowUnary,
      netUnary, uniformUnary, consumerUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
