import BEDC.Derived.ClosedBoundedIntervalUp.DensityLedger

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_density_readback [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName meshRead densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalDensityLedger lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName meshRead densityRead bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row densityRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle densityRead pkg)
          hsame ∧
        UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _endpointRoute, _containmentRoute, meshRoute,
    densityRoute, _replayRoute, densityPkg⟩ := ledger
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed dyadicUnary streamUnary meshRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed meshUnary readbackUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row densityRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro densityRead ⟨hsame_refl densityRead, densityUnary⟩
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
      exact ⟨source.right, densityPkg⟩
  }
  exact ⟨cert, densityUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
