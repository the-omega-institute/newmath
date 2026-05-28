import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_located_cover_handoff [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont dyadic stream coverRead →
        PkgSig bundle coverRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                  hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row coverRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle coverRead pkg ∧ Cont dyadic stream coverRead)
              hsame ∧ UnaryHistory coverRead ∧ Cont dyadic stream coverRead ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle coverRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet coverRoute coverPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed dyadicUnary streamUnary coverRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨
              hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row readback ∨ hsame row sealRow ∨ hsame row coverRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle coverRead pkg ∧ Cont dyadic stream coverRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverRead ⟨hsame_refl coverRead, coverUnary⟩
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
      exact ⟨source.right, coverPkg, coverRoute⟩
  }
  exact ⟨cert, coverUnary, coverRoute, provenancePkg, coverPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
