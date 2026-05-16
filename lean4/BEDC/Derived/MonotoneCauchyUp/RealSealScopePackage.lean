import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_real_seal_scope_package [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont interval realSeal sealRead ->
        Cont sealRead nameRow publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
              (fun row : BHist =>
                Cont interval realSeal sealRead ∧ Cont sealRead nameRow publicRead ∧
                  hsame row publicRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier intervalSealRead sealNamePublic publicPkg
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    _transportRouteProvenance, _nameRowPkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary nameRowUnary sealNamePublic
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro (hsame_refl publicRead) publicPkg)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact ⟨intervalSealRead, sealNamePublic, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport publicReadUnary (hsame_symm source.left), publicPkg⟩
  }

end BEDC.Derived.MonotoneCauchyUp
