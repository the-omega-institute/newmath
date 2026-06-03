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

theorem ClosedBoundedIntervalPacket_cauchy_modulus_nonescape [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported modulusRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream modulusRead ->
        Cont modulusRead readback cauchyRead ->
          PkgSig bundle cauchyRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
                    hsame row modulusRead ∨ hsame row cauchyRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle cauchyRead pkg)
                hsame ∧
              UnaryHistory modulusRead ∧ UnaryHistory cauchyRead ∧
                Cont dyadic stream modulusRead ∧ Cont modulusRead readback cauchyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet modulusRoute cauchyRoute cauchyPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed dyadicUnary streamUnary modulusRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed modulusUnary readbackUnary cauchyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
              hsame row modulusRead ∨ hsame row cauchyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle cauchyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cauchyRead ⟨hsame_refl cauchyRead, cauchyUnary⟩
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
      exact ⟨source.right, provenancePkg, cauchyPkg⟩
  }
  exact ⟨cert, modulusUnary, cauchyUnary, modulusRoute, cauchyRoute⟩

end BEDC.Derived.ClosedboundedintervalUp
