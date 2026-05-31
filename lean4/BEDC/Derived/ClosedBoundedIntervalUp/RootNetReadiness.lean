import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_net_readiness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported meshCenter coverageRead netReady : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream meshCenter ->
        Cont meshCenter readback coverageRead ->
          Cont coverageRead sealRow netReady ->
            PkgSig bundle netReady pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row netReady ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                      hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row readback ∨ hsame row sealRow ∨ hsame row netReady)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle netReady pkg)
                  hsame ∧
                UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
                  UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory meshCenter ∧
                      UnaryHistory coverageRead ∧ UnaryHistory netReady := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet meshRoute coverageRoute netRoute netPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, _provenancePkg, _localNamePkg⟩ := packet
  have meshUnary : UnaryHistory meshCenter :=
    unary_cont_closed dyadicUnary streamUnary meshRoute
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed meshUnary readbackUnary coverageRoute
  have netUnary : UnaryHistory netReady :=
    unary_cont_closed coverageUnary sealUnary netRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row netReady ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row netReady)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle netReady pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro netReady ⟨hsame_refl netReady, netUnary⟩
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
      exact ⟨source.right, netPkg⟩
  }
  exact
    ⟨cert, lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealUnary, meshUnary, coverageUnary, netUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
