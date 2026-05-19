import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_public_tail_window_certificate [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont schedule modulus commonWindow ->
        Cont interval realSeal sealRead ->
          Cont commonWindow sealRead publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal
                    transportRow route provenance nameRow bundle pkg ∧ hsame row publicRead)
                (fun row : BHist =>
                  Cont schedule modulus commonWindow ∧ Cont interval realSeal sealRead ∧
                    Cont commonWindow sealRead row ∧ Cont transportRow route provenance ∧
                      PkgSig bundle publicRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier scheduleModulusCommonWindow intervalRealSealRead commonSealPublicRead
    publicPkg
  have carrierWitness := carrier
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    transportRouteProvenance, _nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommonWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed commonWindowUnary sealReadUnary commonSealPublicRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro carrierWitness (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨scheduleModulusCommonWindow, intervalRealSealRead,
          cont_result_hsame_transport commonSealPublicRead (hsame_symm source.right),
          transportRouteProvenance, publicPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport publicReadUnary (hsame_symm source.right), publicPkg⟩
  }

theorem MonotoneCauchyCarrier_interval_real_seal_route_certificate [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg →
      Cont interval realSeal sealRead →
        Cont sealRead nameRow publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory interval ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
              UnaryHistory publicRead ∧ Cont interval realSeal sealRead ∧
                Cont sealRead nameRow publicRead ∧ Cont transportRow route provenance ∧
                  PkgSig bundle nameRow pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier intervalRealSealRead sealNamePublic publicPkg
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary nameRowUnary sealNamePublic
  exact
    ⟨intervalUnary, realSealUnary, sealReadUnary, publicReadUnary, intervalRealSealRead,
      sealNamePublic, transportRouteProvenance, nameRowPkg, publicPkg⟩

end BEDC.Derived.MonotoneCauchyUp
