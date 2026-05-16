import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_scoped_tail_window_package [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      commonWindow trapRead sealRead tailSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont schedule modulus commonWindow ->
        Cont ledger interval trapRead ->
          Cont interval realSeal sealRead ->
            Cont commonWindow sealRead tailSeal ->
              Cont tailSeal transportRow publicRead ->
                PkgSig bundle tailSeal pkg ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row tailSeal ∧ PkgSig bundle tailSeal pkg)
                      (fun row : BHist =>
                        Cont schedule modulus commonWindow ∧ Cont ledger interval trapRead ∧
                          Cont interval realSeal sealRead ∧
                            Cont commonWindow sealRead tailSeal ∧ hsame row tailSeal)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleModulusCommon ledgerIntervalTrap intervalRealSealRead
    commonSealTail tailTransportPublic tailPkg publicPkg
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    realSealUnary, transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    _transportRouteProvenance, _nameRowPkg⟩ := carrier
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommon
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have tailSealUnary : UnaryHistory tailSeal :=
    unary_cont_closed commonWindowUnary sealReadUnary commonSealTail
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed tailSealUnary transportRowUnary tailTransportPublic
  exact {
    core := {
      carrier_inhabited := Exists.intro tailSeal ⟨hsame_refl tailSeal, tailPkg⟩
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
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨scheduleModulusCommon, ledgerIntervalTrap, intervalRealSealRead,
        commonSealTail, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport tailSealUnary (hsame_symm source.left), publicPkg⟩
  }

end BEDC.Derived.MonotoneCauchyUp
