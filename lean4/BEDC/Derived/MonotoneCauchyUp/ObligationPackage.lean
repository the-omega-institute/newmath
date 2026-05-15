import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_obligation_package [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance
      nameRow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      Cont nameRow provenance publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal
                transportRow route provenance nameRow bundle pkg ∧ hsame row publicRead)
            (fun row : BHist =>
              hsame row publicRead ∧ Cont regular schedule modulus ∧
                Cont modulus ledger interval ∧ Cont interval realSeal nameRow ∧
                  Cont nameRow provenance publicRead)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier namePublicCont publicPkg
  obtain ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary,
    realSealUnary, transportRowUnary, routeUnary, provenanceUnary, nameRowUnary,
    regularScheduleModulus, modulusLedgerInterval, intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := carrier
  have carrierPacket :
      MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow
        route provenance nameRow bundle pkg :=
    ⟨regularUnary, scheduleUnary, modulusUnary, ledgerUnary, intervalUnary, realSealUnary,
      transportRowUnary, routeUnary, provenanceUnary, nameRowUnary, regularScheduleModulus,
      modulusLedgerInterval, intervalRealSealNameRow, transportRouteProvenance, nameRowPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed nameRowUnary provenanceUnary namePublicCont
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro carrierPacket (hsame_refl publicRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.right, regularScheduleModulus, modulusLedgerInterval,
          intervalRealSealNameRow, namePublicCont⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport publicUnary (hsame_symm source.right), publicPkg⟩
  }

end BEDC.Derived.MonotoneCauchyUp
