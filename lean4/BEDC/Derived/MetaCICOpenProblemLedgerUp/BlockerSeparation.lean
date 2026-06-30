import BEDC.Derived.MetaCICOpenProblemLedgerUp

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICOpenProblemLedger_blocker_separation [AskSetup] [PackageSetup]
    {S C N U D E B H R P Q blockerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICOpenProblemLedgerCarrier S C N U D E B H R P Q bundle pkg ->
      Cont B H blockerRead ->
        PkgSig bundle blockerRead pkg ->
          hsame blockerRead R ∧ UnaryHistory B ∧ UnaryHistory H ∧ UnaryHistory R ∧
            UnaryHistory blockerRead ∧ Cont B H R ∧ Cont B H blockerRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle Q pkg ∧
                PkgSig bundle blockerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory hsame
  intro carrier blockerRoute blockerPkg
  obtain ⟨_sUnary, _cUnary, _nUnary, _uUnary, _dUnary, _eUnary, bUnary, hUnary,
    rUnary, _pUnary, _qUnary, _subjectRoute, _decidableRoute, blockerReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have blockerSameR : hsame blockerRead R :=
    hsame_symm (cont_deterministic blockerReplay blockerRoute)
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed bUnary hUnary blockerRoute
  exact
    ⟨blockerSameR, bUnary, hUnary, rUnary, blockerUnary, blockerReplay, blockerRoute,
      provenancePkg, localNamePkg, blockerPkg⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
