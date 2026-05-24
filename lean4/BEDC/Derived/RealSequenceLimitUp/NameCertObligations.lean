import BEDC.Derived.RealSequenceLimitUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSequenceLimitCarrier [AskSetup] [PackageSetup]
    (sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sequenceRow ∧ UnaryHistory limitRow ∧ UnaryHistory windowSchedule ∧
    UnaryHistory dyadicLedger ∧ UnaryHistory classifierRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont sequenceRow windowSchedule route ∧ Cont limitRow dyadicLedger classifierRow ∧
          hsame transport BHist.Empty ∧ hsame route classifierRow ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem RealSequenceLimitNameCert_obligation_surface [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger
            classifierRow transport route provenance name bundle pkg ∧ hsame row classifierRow)
        (fun row : BHist =>
          RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger
            classifierRow transport route provenance name bundle pkg ∧ hsame row classifierRow)
        (fun row : BHist =>
          RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger
            classifierRow transport route provenance name bundle pkg ∧ hsame row classifierRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro classifierRow ⟨carrier, hsame_refl classifierRow⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem RealSequenceLimit_regular_tail_scope_lock [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name tailWindow tailRead tailSeal exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg →
      Cont windowSchedule dyadicLedger tailWindow →
        Cont tailWindow classifierRow tailRead →
          Cont tailRead route tailSeal →
            Cont tailSeal name exported →
              PkgSig bundle exported pkg →
                UnaryHistory windowSchedule ∧ UnaryHistory dyadicLedger ∧
                  UnaryHistory tailWindow ∧ UnaryHistory tailRead ∧ UnaryHistory tailSeal ∧
                    UnaryHistory exported ∧ Cont windowSchedule dyadicLedger tailWindow ∧
                      Cont tailWindow classifierRow tailRead ∧ Cont tailRead route tailSeal ∧
                        Cont tailSeal name exported ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier tailWindowRoute tailReadRoute tailSealRoute exportRoute exportedPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary,
      _transportUnary, routeUnary, _provenanceUnary, nameUnary, _sequenceRoute,
      _classifierRoute, _transportSame, _routeSame, provenancePkg, _namePkg⟩
  have tailWindowUnary : UnaryHistory tailWindow :=
    unary_cont_closed windowUnary dyadicUnary tailWindowRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed tailWindowUnary classifierUnary tailReadRoute
  have tailSealUnary : UnaryHistory tailSeal :=
    unary_cont_closed tailReadUnary routeUnary tailSealRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed tailSealUnary nameUnary exportRoute
  exact
    ⟨windowUnary, dyadicUnary, tailWindowUnary, tailReadUnary, tailSealUnary,
      exportedUnary, tailWindowRoute, tailReadRoute, tailSealRoute, exportRoute,
      provenancePkg, exportedPkg⟩

end BEDC.Derived.RealSequenceLimitUp
